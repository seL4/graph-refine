#!/usr/bin/env python3

# Copyright (c) 2022, Kry10 Limited
# SPDX-License-Identifier: BSD-2-Clause

import enum
import re
import os
import sys
import yaml

from collections import Counter
from datetime import datetime, timezone
from enum import Enum
from lxml import etree
from pathlib import Path
from textwrap import dedent
from typing import Dict, Mapping, NamedTuple, Optional, Sequence, TextIO
from yaml import CLoader as YamlLoader


class Trigger(NamedTuple):
    repo: str
    run_id: int


@enum.unique
class Status(Enum):
    Passed = 1
    Failed = 2
    Skipped = 3
    Running = 4
    Queued = 5
    Unknown = 6


class JobInfo(NamedTuple):
    submitted: datetime
    triggers: Sequence[Trigger]
    sel4: str
    functions: Mapping[str, Mapping[str, Status]]
    counter: Counter[Status]


def unlines(*lines: str) -> str:
    ''.join(f'{line}\n' for line in lines)


def config_header(config: str) -> str:
    return f'<h1>{config}</h1>\n<table>\n'


def config_footer(config: str) -> str:
    return f'</table>\n\n'


def fun_data(config: str, function: str, status: Status) -> str:
    if status != Status.Queued:
        return ' '.join(
            f'<a href="configs/{config}/functions/{function}/{log}.txt">{log}</a>'
            for log in ['log', 'report'])
    else:
        return ''


def render_job(job_html: TextIO, job_id: str, info: JobInfo) -> None:
    for config, functions in info.functions.items():
        job_html.write(config_header(config))
        for function, status in functions.items():
            job_html.write(dedent(f'''
                <tr>
                  <td>{function}</td>
                  <td class="status {status.name}">{status.name}</td>
                  <td>{fun_data(config, function, status)}</td>
                </tr>
                ''').lstrip())
        job_html.write(config_footer(config))


status_headers = '\n          '.join(f'<th>{status.name}</th>' for status in Status)
index_header = dedent(f'''
    <!DOCTYPE html>
    <html>
      <head><title>seL4 binary verification</title></head>
      <body><table>
        <tr>
          <th>Job submitted</th>
          <th>Triggered by</th>
          <th>seL4 commit</th>
          {status_headers}
          <th>Configs</th>
        </tr>
    ''')
index_footer = '  </table></body>\n</html>\n'


def td(text: str, cls: Optional[str] = None) -> str:
    return f'<td>{text}</td>' if cls is None else f'<td class="{cls}">{text}</td>'


def trigger_a(trigger: Trigger) -> str:
    return f'<a href="https://github.com/{trigger.repo}/actions/runs/{trigger.run_id}">{trigger.run_id}</a>'


def triggers_td(triggers: Sequence[Trigger]) -> str:
    return td(' '.join(trigger_a(trigger) for trigger in triggers))


def submit_td(job_id: str, time: datetime) -> str:
    return td(f'<a href="jobs/{job_id}/">{time:%Y-%m-%d %H:%M:%S}</a>')


def sel4_td(sha: str) -> str:
    return td(f'<a href="https://github.com/seL4/seL4/commit/{sha}">{sha[:16]}</a>')


def status_td(status: Status, count: int) -> str:
    return td(f'{count}', cls=f'status {status.name}') if count else td('')


def counter_tds(counter: Counter[Status]) -> Sequence[str]:
    return [status_td(status, counter[status]) for status in Status]


def configs_td(functions: Mapping[str, Mapping[str, Status]]) -> str:
    configs = set(config[:config.rfind('-')] for config in functions)
    return td(' '.join(configs))


def job_summary(job_id: str, info: JobInfo) -> str:
    tds = '\n      '.join([submit_td(job_id, info.submitted),
                           triggers_td(info.triggers),
                           sel4_td(info.sel4),
                           *counter_tds(info.counter),
                           configs_td(info.functions)])
    return f'    <tr>\n      {tds}\n    </tr>\n'


def render_jobs(work_dir: Path, jobs: Mapping[str, JobInfo]) -> None:
    with open(work_dir / 'index.html.tmp', 'w') as index_html:
        index_html.write(index_header)
        for job_id, job_info in jobs.items():
            index_html.write(job_summary(job_id, job_info))
            job_dir = work_dir / 'jobs' / job_id
            with open(job_dir / 'index.html.tmp', 'w') as job_html:
                render_job(job_html, job_id, job_info)
            (job_dir / 'index.html.tmp').rename(job_dir / 'index.html')
        index_html.write(index_footer)
    (work_dir / 'index.html.tmp').rename(work_dir / 'index.html')


result_re = re.compile(
    r'Result (?P<result>\w+) for pair Pairing \((?P<name>\w+) \(ASM\) <= \S+ \(C\)\), time taken: .*')
abort_re = re.compile(
    r'Aborting Problem \(Pairing \((?P<name>\S+) \(ASM\) <= \S+ \(C\)\)\).*')


def get_job(job_id: str, job_dir: Path) -> JobInfo:
    # Get submit time
    with open(job_dir / 'submitted.yaml') as manifest:
        data = yaml.load(manifest, Loader=YamlLoader)
        submitted = datetime.fromtimestamp(data['timestamp'], tz=timezone.utc)
    # Get triggers
    with open(job_dir / 'decompile-manifest.yaml') as manifest:
        data = yaml.load(manifest, Loader=YamlLoader)
        triggers = [Trigger(repo=data[t]['repo'], run_id=data[t]['run_id'])
                    for t in ['triggered-by', 'workflow']]
    # Get seL4 commit
    with open(job_dir / 'verification-manifest.xml') as manifest:
        data = etree.parse(manifest)
        sel4 = data.xpath('string(//project[@name="seL4"]/@revision)')

    functions: Dict[str, Dict[str, Status]] = {}
    counter: Counter[Status] = Counter()

    # Work through configs
    for entry in os.scandir(job_dir / 'configs'):
        config = entry.name
        config_dir = job_dir / 'configs' / config

        def add_fun(name: str, status: Status) -> None:
            functions.setdefault(config, {})[name] = status
            counter.update([status])

        def file_report(name: str) -> None:
            fun_dir = config_dir / 'functions' / function_name
            report = fun_dir / 'report.txt'
            if report.is_file():
                with open(report) as report_file:
                    for report_line in report_file:
                        report_line = report_line.strip()
                        match = result_re.fullmatch(report_line)
                        if match:
                            assert match['name'] == name
                            if match['result'] == 'True':
                                add_fun(name, Status.Passed)
                            elif match['result'] == 'False':
                                add_fun(name, Status.Failed)
                            else:
                                add_fun(name, Status.Unknown)
                            return
                        match = abort_re.fullmatch(report_line)
                        if match:
                            assert match['name'] == name
                            add_fun(name, Status.Skipped)
                            return
            if fun_dir.is_dir():
                add_fun(name, Status.Unknown)

        with open(config_dir / 'target' / 'functions.txt') as functions_txt:
            for function_name in functions_txt:
                function_name = function_name.strip()
                if (config_dir / 'waiting' / function_name).exists():
                    add_fun(function_name, Status.Queued)
                elif (config_dir / 'working' / function_name).exists():
                    counter.update(running=1)
                    add_fun(function_name, Status.Running)
                else:
                    file_report(function_name)

    return JobInfo(submitted=submitted,
                   triggers=triggers,
                   sel4=sel4,
                   functions=functions,
                   counter=counter)


def main(work_dir: Path) -> None:
    with open(work_dir / 'jobs.txt') as jobs_file:
        jobs = {job_id: get_job(job_id, work_dir / 'jobs' / job_id)
                for job_id in (job_line.strip()
                               for job_line in jobs_file)}
    render_jobs(work_dir, jobs)


if __name__ == '__main__':
    assert len(sys.argv) == 2
    main(Path(sys.argv[1]))
