#!/usr/bin/env python3

import json
import os
import shutil
import sys

from lxml import etree  # type: ignore
from pathlib import Path
from typing import Any


supported_targets = (
    'ARM-O1',
    'ARM-O2',
    'ARM-MCS-O1',
    'ARM-MCS-O2',
    'RISCV64-O1',
    'RISCV64-MCS-O1',
)


def workflow_url(repo: str, run: str) -> str:
  return f'https://github.com/{repo}/actions/runs/{run}'


artifacts_input_dir = Path(sys.argv[1]).resolve()
job_output_dir = Path(sys.argv[2]).resolve()

targets: dict[str, Any] = {}

for target in supported_targets:
    artifact_path = artifacts_input_dir / target
    print(f'Checking artifact_path {artifact_path}')
    if (artifact_path / 'CFunctions.txt').is_file():
        print('Found CFunctions.txt')
        target_path = job_output_dir / 'targets' / target
        target_path.mkdir(parents=True)
        print(f'Target path {target_path}')
        shutil.move(artifact_path, target_path / 'target')

        def get_var(line: str) -> tuple[str, str]:
            parts = [s.strip() for s in line.split(sep='=', maxsplit=1)]
            assert len(parts) == 2
            return parts[0], parts[1]

        with open(target_path / 'target' / 'config.env') as config_env:
            config = dict(get_var(line) for line in config_env)

        with open(target_path / 'target' / 'manifest.xml') as manifest_xml:
            manifest = etree.parse(manifest_xml)
            versions = {'seL4': manifest.xpath(f'string(//project[@name="seL4"]/@revision)'),
                        'l4v': manifest.xpath(f'string(//project[@name="l4v"]/@revision)')}

        targets[target] = {'config': config, 'versions': versions}

if targets:
    with open(job_output_dir / 'job_info.json', 'w') as job_info_json:
        github_info = {'tag': os.environ['TAG'],
                       'proof': {'repo': os.environ['PROOF_REPO'],
                                 'run': os.environ['PROOF_RUN']},
                       'decompile': {'repo': os.environ['DECOMPILE_REPO'],
                                     'run': os.environ['DECOMPILE_RUN']}}
        job_info = {'targets': targets, 'github': github_info}
        json.dump(job_info, job_info_json, separators=(',', ':'))

with open(os.environ['GITHUB_OUTPUT'], 'a') as github_output:
    enabled_json = json.dumps(list(targets), separators=(',', ':'))
    print(f'targets_enabled={enabled_json}', file=github_output)
