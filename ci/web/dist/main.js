const jobs_index_sections = [
  { label: "running", title: "Running jobs" },
  { label: "waiting", title: "Waiting jobs" },
  { label: "finished", title: "Recently finished jobs" },
];

const job_status_classification = new Map([
  ["WAITING", "waiting"],
  ["RUNNING", "running"],
  ["PASSED", "passed"],
  ["UNDERSPECIFIED", "passed"],
  ["COMPLEX_LOOP", "passed"],
  ["IMPOSSIBLE", "passed"],
  ["FAILED", "failed"],
  ["NO_SPLIT", "failed"],
  ["EXCEPT", "failed"],
  ["TIMEOUT", "failed"],
  ["MALFORMED", "failed"],
  ["NO_RESULT", "failed"],
  ["KILLED", "failed"],
]);

const function_result_classification = new Map([
  ["PASSED", { group: "passed" }],
  ["UNDERSPECIFIED", { group: "skipped", detail: "underspecified function" }],
  ["COMPLEX_LOOP", { group: "skipped", detail: "complex loop" }],
  ["IMPOSSIBLE", { group: "skipped", detail: "underspecified function" }],
  ["FAILED", { group: "failed", detail: "failed refinement" }],
  ["NO_SPLIT", { group: "failed", detail: "failed to split loop" }],
  ["EXCEPT", { group: "failed", detail: "exception" }],
  ["TIMEOUT", { group: "failed", detail: "timeout" }],
  ["MALFORMED", { group: "failed", detail: "malformed report" }],
  ["NO_RESULT", { group: "failed", detail: "no group found" }],
  ["KILLED", { group: "failed", detail: "killed" }],
]);

function on(f) {
  return (a, b) => f(a) < f(b) ? -1 : f(b) < f(a) ? 1 : 0;
}

function esc_html(s) {
  return String(s).replaceAll('&', '&amp;')
                  .replaceAll('<', '&lt;')
                  .replaceAll('>', '&gt;')
                  .replaceAll('"', '&quot;');
}

async function fetch_json(url) {
  return await fetch(url).then(r => r.json());
}

function zpad(n, len) {
  return String(n).padStart(len, '0');
}

function date_time(date_str) {
  const d = new Date(date_str);
  return `${zpad(d.getFullYear(), 2)}-${zpad(d.getMonth() + 1, 2)}-${zpad(d.getDate(), 2)}`
    + ` ${zpad(d.getHours(), 2)}:${zpad(d.getMinutes(), 2)}`;
}

function time_diff_ms(t1, t2) {
  const d1 = new Date(t1);
  const d2 = (t2 === undefined || t2 === null) ? new Date() : new Date(t2);
  return d2 - d1;
}

function time_diff_str(t1, t2) {
  const seconds = time_diff_ms(t1, t2) / 1000;
  if (seconds < 90) {
    return `${seconds.toFixed(0)}s`;
  }
  const minutes = seconds / 60;
  if (minutes < 90) {
    return `${minutes.toFixed(0)}m`;
  }
  const hours = minutes / 60;
  if (hours < 36) {
    return `${hours.toFixed(0)}h`;
  }
  const days = hours / 24;
  return `${days.toFixed(0)}d`;
}

function date_markup(title, date) {
  return date === null ? '' : `
    <div class="w-40">
      <div class="text-xs text-slate-400">${title}</div>
      <div class="font-mono">${date_time(date)}</div>
    </div>
  `;
}

function github_run(title, {repo, run}) {
  return `
    <div class="w-40">
      <div class="text-xs text-slate-400">${title}</div>
      <div class="font-mono">
        <a href="https://github.com/${repo}/actions/runs/${run}" class="hover:underline">${run}</a>
      </div>
    </div>
  `;
}

async function job_list_item(job_id) {
  const [job_info, job_status] = await Promise.all([
    fetch_json(`jobs/${job_id}/job_info.json`),
    fetch_json(`jobs/${job_id}/job_status.json`)
  ]);

  const targets = Object.entries(job_status.targets).map(([target, status]) => {
    const status_map = new Map();
    Object.entries(status).forEach(([status, count]) => {
      const group = job_status_classification.get(status) ?? "failed";
      status_map.set(group, (status_map.get(group) ?? 0) + count);
    });
    function render_status(s) {
      return `
        <div class="w-40">
          <div class="text-xs text-slate-400">${s}</div>
          <div class="font-mono">${status_map.get(s) ?? 0}</div>
        </div>
      `;
    }
    return { target, content: `
      <div class="mt-1 pt-1 flex flex-wrap gap-x-8 gap-y-1">
        <div class="w-40">
          <div class="text-xs text-slate-400">target</div>
          <div class="font-mono"><a href="?job_id=${job_id}&target=${target}" class="hover:underline">${target}</a></div>
        </div>
        <div class="flex flex-wrap gap-x-8 gap-y-1">
          <div class="flex flex-wrap gap-x-8 gap-y-1">
            ${render_status("waiting")}
            ${render_status("running")}
          </div>
          <div class="flex flex-wrap gap-x-8 gap-y-1">
            ${render_status("passed")}
            ${render_status("failed")}
          </div>
        </div>
      </div>
    `};
  });

  targets.sort(on(s => s.target));

  return `
    <div class="grid grid-cols-1 divide-y divide-slate-600 gap-y-1 -mx-2 my-3 px-2 py-2 rounded-md bg-slate-800 hover:ring-1 hover:ring-slate-400">
      <div class="flex flex-wrap gap-x-8 gap-y-1">
        <div class="w-40">
          <div class="text-xs text-slate-400">job id</div>
          <div class="font-mono">${job_id.substring(0,10)}</div>
        </div>
        <div class="flex flex-wrap gap-x-8 gap-y-1">
          <div class="flex flex-wrap gap-x-8 gap-y-1">
            ${date_markup("submitted", job_status.timestamps.time_job_submitted)}
            ${date_markup("started", job_status.timestamps.time_job_started)}
            ${date_markup("finished", job_status.timestamps.time_job_finished)}
          </div>
          <div class="flex flex-wrap gap-x-8 gap-y-1">
            ${github_run("proof run", job_info.github.proof)}
            ${github_run("decompile run", job_info.github.decompile)}
          </div>
        </div>
      </div>
      ${targets.map(s => s.content).join('')}
    </div>
  `;
}

async function job_list({label, title, job_ids}) {
  const job_items = await Promise.all(job_ids.map(job_list_item));

  return job_ids.length === 0 ? '' : `
    <section class="mt-6">
      <h2 class="text-xl font-bold">${title}</h2>
      ${job_items.join('')}
    </section>
  `;
}

async function render_index() {
  const jobs_json = await fetch_json('jobs.json');

  const section_data = jobs_index_sections.flatMap(
    ({label, title}) => ({label, title, job_ids: jobs_json[label].map(job => job.job_id)})
  );

  const jobs_lists = await Promise.all(section_data.map(job_list));
  document.getElementById("content-container").innerHTML = jobs_lists.join('');
}

async function render_job(job_id) {

}

async function render_target(job_id, target) {
  const [job_info, job_status, functions_status] = await Promise.all([
    fetch_json(`jobs/${job_id}/job_info.json`),
    fetch_json(`jobs/${job_id}/job_status.json`),
    fetch_json(`jobs/${job_id}/targets/${target}/functions.json`)
  ]);

  const versions = job_info.targets[target].versions;

  const waiting_functions = [];
  const running_functions = [];

  const passed_functions = [];
  const failed_functions = [];
  const skipped_functions = [];

  Object.entries(functions_status).forEach(([name, info]) => {
    const runner_id = info.assignment?.runner_id;
    const run_id = info.assignment?.run_id;
    const run_info = info.runs?.[runner_id]?.[run_id];
    const started = run_info?.time_run_started;
    const finished = run_info?.time_run_finished;
    const result = run_info?.result;

    function fun_name_cell({indicator_colour}) {
      const indicator = `<span class="w-2 h-2 align-baseline mr-2 ${indicator_colour} rounded-full inline-block"></span>`;
      return indicator + name;
    }

    if (started === undefined) {
      waiting_functions.push({name, content: `
        <tr class="hover:text-semibold">
          <td class="px-2 py-1">${fun_name_cell(config)}</td>
        </tr>
      `});
      return;
    }

    function report_log_cell() {
      const fun_url = `jobs/${job_id}/targets/${target}/functions/${name}/${run_id}`;
      const link = s => `<a href="${fun_url}/${s}.txt" class="hover:underline">${s}</a>`; 
      return `${link("report")} ${link("log")}`;
    }

    function fun_row(config) {
      return {name, content: `
        <tr class="hover:bg-slate-700">
          <td class="px-2 py-1">${fun_name_cell(config)}</td>
          <td class="px-2 py-1 w-56">${config.detail === undefined ? '' : config.detail}</td>
          <td class="px-2 py-1 w-32 text-right">${report_log_cell()}</td>
          <td class="px-2 py-1 w-16 font-mono text-right">${time_diff_str(started, finished)}</td>
        </tr>
      `};
    }

    if (result === null && finished === null) {
      running_functions.push(fun_row({indicator_colour: "bg-gray-500"}));
      return;
    }

    const {group, detail} = function_result_classification.get(result) ?? {
      group: "failed", detail: "internal error"
    };

    if (group === "passed") {
      passed_functions.push(fun_row({indicator_colour: "bg-green-500"}));
      return;
    }

    if (group === "failed") {
      failed_functions.push(fun_row({detail, indicator_colour: "bg-red-500"}));
      return;
    }

    if (group === "skipped") {
      skipped_functions.push(fun_row({detail, indicator_colour: "bg-amber-500"}));
      return;
    }
  });

  waiting_functions.sort(on(f => f.name));
  running_functions.sort(on(f => f.name));
  passed_functions.sort(on(f => f.name));
  failed_functions.sort(on(f => f.name));
  skipped_functions.sort(on(f => f.name));

  function function_count(arr) {
    return arr.length === 1 ? "1 function" : `${arr.length} functions`;
  }

  function render_functions(group, arr) {
    return arr.length === 0 ? '' : `
      <details class="mt-5" open>
        <summary class="text-xl font-bold">${function_count(arr)} ${group}</summary>
        <div class="grid grid-cols-1 -mx-2 my-3 py-1 rounded-md bg-slate-800">
          <table class="w-full">
            <tbody>
              ${arr.map(f => f.content).join('')}
            </tbody>
          </table>
        </div>
      </details>
    `;
  }

  document.getElementById("content-container").innerHTML = `
    <section class="mt-6">
      <h2 class="text-xl font-bold">Target detail</h2>
      <div class="grid grid-cols-1 gap-y-3 -mx-2 mt-3 mb-8 px-2 py-2 rounded-md bg-slate-800">
        <div class="flex flex-wrap gap-x-8 gap-y-3">
          <div class="w-40">
            <div class="text-xs text-slate-400">job id</div>
            <div class="font-mono">${job_id.substring(0,10)}</div>
          </div>
          <div class="w-40">
            <div class="text-xs text-slate-400">target</div>
            <div class="font-mono">${target}</div>
          </div>
          <div>
            <div class="text-xs text-slate-400">job tag</div>
            <div class="font-mono">${esc_html(job_info.github.tag)}</div>
          </div>
        </div>
        <div class="flex flex-wrap gap-x-8 gap-y-3">
          ${date_markup("submitted", job_status.timestamps.time_job_submitted)}
          ${date_markup("started", job_status.timestamps.time_job_started)}
          ${date_markup("finished", job_status.timestamps.time_job_finished)}
        </div>
        <div class="flex flex-wrap gap-x-8 gap-y-3">
          ${github_run("proof run", job_info.github.proof)}
          ${github_run("decompile run", job_info.github.decompile)}
          <div class="w-40">
            <div class="text-xs text-slate-400">seL4 commit</div>
            <div class="font-mono">${versions["seL4"].substring(0,10)}</div>
          </div>
          <div class="w-40">
            <div class="text-xs text-slate-400">l4v commit</div>
            <div class="font-mono">${versions["l4v"].substring(0,10)}</div>
          </div>
        </div>
      </div>
      ${render_functions("failed", failed_functions)}
      ${render_functions("passed", passed_functions)}
      ${render_functions("running", running_functions)}
      ${render_functions("waiting", waiting_functions)}
      ${render_functions("skipped", skipped_functions)}
    </section>
  `;
}

async function render_content() {
  const params = new URLSearchParams(window.location.search);
  const job_id = params.get("job_id");
  const target = params.get("target");
  await (job_id === null || target === null) ? render_index() : render_target(job_id, target);
}

render_content();
