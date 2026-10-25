(() => {
  "use strict";

  const $ = (selector) => document.querySelector(selector);
  const els = {
    input: $("#array-input"), inputError: $("#input-error"), chart: $("#chart"),
    count: $("#array-count"), statusPill: $("#status-pill"), comparisons: $("#comparisons"),
    swaps: $("#swaps"), shifts: $("#shifts"), writes: $("#writes"), currentStep: $("#current-step"),
    totalSteps: $("#total-steps"), status: $("#execution-status"), play: $("#play-btn"),
    pause: $("#pause-btn"), step: $("#step-btn"), reset: $("#reset-btn"), speed: $("#speed-select"),
    completion: $("#completion"), originalResult: $("#original-result"), sortedResult: $("#sorted-result"),
    title: $("#algorithm-title"), overview: $("#overview"), how: $("#how-it-works"),
    strategy: $("#strategy"), stable: $("#stable"), best: $("#best-complexity"),
    average: $("#average-complexity"), worst: $("#worst-complexity"), complexityNote: $("#complexity-note"),
    pseudocode: $("#pseudocode"), log: $("#operation-log"), logCount: $("#log-count")
  };

  const ALGORITHMS = {
    bubble: {
      name: "Bubble Sort", strategy: "Adjacent exchanges", stable: "Yes",
      best: "O(n)", average: "O(n²)", worst: "O(n²)",
      note: "Bubble Sort reaches O(n) in the best case because this implementation stops early when a pass makes no swaps.",
      overview: "Bubble Sort repeatedly compares neighboring values and swaps them when they are out of order. Large values gradually move toward the end.",
      how: ["Compare two neighboring elements.", "Swap them if the left value is larger.", "Repeat passes until no swaps are needed."],
      code: ["for each pass through the array", "  swapped = false", "  compare each adjacent pair", "  if left value > right value", "    swap the pair; swapped = true", "  if swapped is false, stop"]
    },
    selection: {
      name: "Selection Sort", strategy: "Select the minimum", stable: "No (standard version)",
      best: "O(n²)", average: "O(n²)", worst: "O(n²)",
      note: "Selection Sort scans the remaining unsorted section on every pass, even when the input is already ordered.",
      overview: "Selection Sort scans the unsorted section to find its smallest value, then places that value at the beginning of the section.",
      how: ["Start at the first unsorted position.", "Scan the rest of the array for the minimum.", "Swap the minimum into the first unsorted position.", "Move the boundary one position right."],
      code: ["for each unsorted start position", "  minimum = start", "  inspect each later element", "  if current < minimum value", "    minimum = current index", "  swap minimum with start if needed"]
    },
    insertion: {
      name: "Insertion Sort", strategy: "Build a sorted prefix", stable: "Yes",
      best: "O(n)", average: "O(n²)", worst: "O(n²)",
      note: "Insertion Sort is O(n) in the best case when the array is already sorted: each key needs only one comparison and no shifts.",
      overview: "Insertion Sort grows a sorted section from left to right. Each new key is compared with earlier values and inserted into the right gap.",
      how: ["Treat the first element as a sorted section.", "Take the next element as the key.", "Shift larger values one position to the right.", "Write the key into the gap."],
      code: ["for each key after the first element", "  key = current element", "  compare key with sorted values", "  while sorted value > key", "    shift sorted value one place right", "  write key into the gap"]
    }
  };

  let algorithm = "bubble";
  let original = [5, 3, 8, 1, 2];
  let events = [];
  let cursor = 0;
  let current = original.slice();
  let running = false;
  let timerId = null;
  let stats = { comparisons: 0, swaps: 0, shifts: 0, writes: 0 };
  let sortedIndices = new Set();
  let latestEvent = null;
  let logEntries = [];
  const MAX_EVENTS = 3000;

  function makeEvent(type, array, meta = {}) {
    return {
      type, array: array.slice(), i: meta.i ?? null, j: meta.j ?? null,
      keyIndex: meta.keyIndex ?? null, minIndex: meta.minIndex ?? null,
      sorted: meta.sorted ? [...meta.sorted] : [], line: meta.line ?? 0,
      description: meta.description || type, stats: { ...meta.stats },
      phase: meta.phase || ""
    };
  }

  // Event generation works on a private copy; rendering only replays recorded states.
  function generateEvents(input, kind) {
    const a = input.slice();
    const list = [];
    const s = { comparisons: 0, swaps: 0, shifts: 0, writes: 0 };
    const sorted = new Set();
    const push = (type, meta = {}) => {
      list.push(makeEvent(type, a, {
        ...meta, sorted: [...sorted], stats: s, phase: meta.phase || kind
      }));
      if (list.length > MAX_EVENTS) throw new Error("Too many visualization events. Try a smaller array.");
    };

    if (kind === "bubble") {
      if (a.length === 1) { sorted.add(0); push("complete", { line: 5, description: "The single element is already sorted." }); return list; }
      for (let end = a.length - 1; end > 0; end--) {
        let swapped = false;
        for (let j = 0; j < end; j++) {
          s.comparisons++;
          push("compare", { i: j, j: j + 1, line: 2, description: `Compared ${a[j]} and ${a[j + 1]}.` });
          if (a[j] > a[j + 1]) {
            push("swap-start", { i: j, j: j + 1, line: 3, description: `${a[j]} is greater than ${a[j + 1]}; swap them.` });
            [a[j], a[j + 1]] = [a[j + 1], a[j]];
            s.swaps++; s.writes += 2; swapped = true;
            push("swap", { i: j, j: j + 1, line: 4, description: `Swapped the pair; ${a[j]} is now before ${a[j + 1]}.` });
          } else push("no-swap", { i: j, j: j + 1, line: 2, description: `No swap needed for ${a[j]} and ${a[j + 1]}.` });
        }
        sorted.add(end);
        push("pass", { i: end, line: 0, description: `${a[end]} is in its final position at index ${end}.` });
        if (!swapped) {
          for (let k = 0; k < end; k++) sorted.add(k);
          push("early-exit", { line: 5, description: "No swaps in this pass, so the array is sorted." });
          return list;
        }
      }
      sorted.add(0);
      push("complete", { line: 5, description: "Every element is in its final position." });
    } else if (kind === "selection") {
      for (let start = 0; start < a.length - 1; start++) {
        let min = start;
        push("minimum", { i: start, minIndex: min, line: 1, description: `Start the scan at ${a[min]}; it is the current minimum.` });
        for (let j = start + 1; j < a.length; j++) {
          s.comparisons++;
          push("compare", { i: j, minIndex: min, line: 2, description: `Compare ${a[j]} with current minimum ${a[min]}.` });
          if (a[j] < a[min]) {
            min = j;
            push("new-minimum", { i: j, minIndex: min, line: 3, description: `New minimum found: ${a[min]}.` });
          }
        }
        if (min !== start) {
          push("swap-start", { i: start, j: min, minIndex: min, line: 5, description: `Place minimum ${a[min]} at index ${start}.` });
          [a[start], a[min]] = [a[min], a[start]];
          s.swaps++; s.writes += 2;
          push("swap", { i: start, j: min, line: 5, description: `Swapped ${a[min]} and ${a[start]}.` });
        } else {
          push("no-swap", { i: start, minIndex: min, line: 5, description: `${a[start]} is already the minimum for this position.` });
        }
        sorted.add(start);
        push("position-sorted", { i: start, line: 5, description: `${a[start]} is fixed in sorted position ${start}.` });
      }
      sorted.add(a.length - 1);
      push("complete", { line: 5, description: "The remaining element is also in its final position." });
    } else {
      if (a.length === 1) { sorted.add(0); push("complete", { line: 5, description: "The single element is already sorted." }); return list; }
      sorted.add(0);
      push("prefix", { i: 0, line: 0, description: `The first element, ${a[0]}, begins the sorted section.` });
      for (let i = 1; i < a.length; i++) {
        const key = a[i];
        let j = i - 1;
        push("key", { i, keyIndex: i, line: 1, description: `Select ${key} as the key to insert.` });
        while (j >= 0) {
          s.comparisons++;
          push("compare", { i: j, j: i, keyIndex: i, line: 2, description: `Compare key ${key} with ${a[j]}.` });
          if (a[j] > key) {
            a[j + 1] = a[j]; s.shifts++; s.writes++;
            push("shift", { i: j, j: j + 1, keyIndex: i, line: 4, description: `Shift ${a[j]} one position to the right.` });
            j--;
          } else {
            push("no-shift", { i: j, keyIndex: i, line: 2, description: `${a[j]} is not greater than ${key}; stop shifting.` });
            break;
          }
        }
        a[j + 1] = key; s.writes++;
        for (let k = 0; k <= i; k++) sorted.add(k);
        push("insert", { i: j + 1, keyIndex: j + 1, line: 5, description: `Write key ${key} into index ${j + 1}.` });
      }
      push("complete", { line: 5, description: "Every key has been inserted into the sorted section." });
    }
    return list;
  }

  function validateArray(text) {
    const trimmed = text.trim();
    if (!trimmed) return { error: "Enter at least 2 comma-separated integers." };
    const tokens = trimmed.split(",");
    if (tokens.length < 2) return { error: "Enter at least 2 values." };
    if (tokens.length > 30) return { error: "Use no more than 30 values." };
    const values = [];
    for (const raw of tokens) {
      const token = raw.trim();
      if (!/^[+-]?\d+$/.test(token)) return { error: `“${token || "(empty)"}” is not an integer. Use commas between whole numbers.` };
      const number = Number(token);
      if (!Number.isSafeInteger(number)) return { error: `“${token}” is outside the safe integer range.` };
      values.push(number);
    }
    return { values };
  }

  function stopPlayback() {
    running = false;
    if (timerId !== null) { clearTimeout(timerId); timerId = null; }
    updateControls();
  }

  function clearLog() {
    logEntries = [];
    renderLog();
  }

  function prepareRun() {
    stopPlayback();
    try { events = generateEvents(original, algorithm); }
    catch (error) { showError(error.message); return false; }
    cursor = 0;
    current = original.slice();
    stats = { comparisons: 0, swaps: 0, shifts: 0, writes: 0 };
    sortedIndices = new Set();
    latestEvent = null;
    clearLog();
    els.completion.hidden = true;
    renderAll();
    updateControls();
    return true;
  }

  function showError(message = "") {
    els.inputError.textContent = message;
    els.input.setAttribute("aria-invalid", message ? "true" : "false");
  }

  function setArray(values) {
    stopPlayback();
    original = values.slice();
    els.input.value = values.join(", ");
    showError("");
    prepareRun();
  }

  function selectAlgorithm(kind) {
    if (!ALGORITHMS[kind]) return;
    algorithm = kind;
    document.querySelectorAll(".algorithm-tab").forEach((button) => {
      const active = button.dataset.algorithm === kind;
      button.classList.toggle("active", active);
      button.setAttribute("aria-pressed", String(active));
    });
    renderAlgorithmInfo();
    prepareRun();
  }

  function renderAlgorithmInfo() {
    const info = ALGORITHMS[algorithm];
    els.title.textContent = info.name;
    els.overview.textContent = info.overview;
    els.strategy.textContent = info.strategy;
    els.stable.textContent = info.stable;
    els.best.textContent = info.best;
    els.average.textContent = info.average;
    els.worst.textContent = info.worst;
    els.complexityNote.textContent = info.note;
    els.how.replaceChildren(...info.how.map((item) => {
      const li = document.createElement("li"); li.textContent = item; return li;
    }));
    els.pseudocode.replaceChildren(...info.code.map((line, index) => {
      const li = document.createElement("li"); li.textContent = line; li.dataset.line = String(index); return li;
    }));
  }

  function barHeight(value, min, max) {
    // Keep every bar anchored to the bottom baseline. Scale by absolute
    // magnitude so negative values do not move the chart baseline.
    const magnitude = Math.max(Math.abs(min), Math.abs(max));
    if (magnitude === 0) return 18;
    return Math.max(8, (Math.abs(value) / magnitude) * 100);
  }

  function renderChart() {
    els.count.textContent = `${current.length} element${current.length === 1 ? "" : "s"}`;
    els.chart.replaceChildren();
    if (!current.length) {
      const empty = document.createElement("div");
      empty.className = "empty-chart";
      empty.textContent = "Apply an array to begin.";
      els.chart.append(empty);
      return;
    }

    const min = Math.min(...current), max = Math.max(...current);
    current.forEach((value, index) => {
      const slot = document.createElement("div");
      slot.className = "bar-slot";
      const bar = document.createElement("div");
      const state = stateFor(index);
      bar.className = `bar${state ? ` ${state}` : ""}${value < 0 ? " negative" : ""}`;
      bar.style.height = `${barHeight(value, min, max)}%`;
      // All bars share the same fixed baseline at the bottom of the chart.
      bar.style.bottom = "0";
      bar.textContent = String(value);
      bar.setAttribute("aria-label", `Index ${index}, value ${value}, ${state || "unsorted"}`);
      const label = document.createElement("span");
      label.className = "bar-label";
      label.textContent = String(index);
      slot.append(bar, label);
      els.chart.append(slot);
    });
    els.chart.setAttribute("aria-label", `Array visualization: ${current.join(", ")}`);
  }

  function stateFor(index) {
    if (!latestEvent) return sortedIndices.has(index) ? "sorted" : "";
    if (latestEvent.type === "complete" || latestEvent.type === "early-exit") return "sorted";
    if (latestEvent.type === "swap" || latestEvent.type === "swap-start" || latestEvent.type === "shift") {
      if (index === latestEvent.i || index === latestEvent.j) return "swap";
    }
    if (latestEvent.keyIndex === index && algorithm === "insertion") return "key";
    if (latestEvent.minIndex === index && algorithm === "selection") return "minimum";
    if ((latestEvent.type === "compare" || latestEvent.type === "no-swap" || latestEvent.type === "no-shift") &&
        (index === latestEvent.i || index === latestEvent.j)) return "compare";
    if (latestEvent.type === "new-minimum" && index === latestEvent.minIndex) return "minimum";
    if (latestEvent.type === "minimum" && index === latestEvent.minIndex) return "minimum";
    return sortedIndices.has(index) ? "sorted" : "";
  }

  function renderStats() {
    els.comparisons.textContent = stats.comparisons;
    els.swaps.textContent = stats.swaps;
    els.shifts.textContent = stats.shifts;
    els.writes.textContent = stats.writes;
    els.currentStep.textContent = cursor;
    els.totalSteps.textContent = events.length;
    const label = running ? "Running" : cursor >= events.length && events.length ? "Complete" : cursor ? "Paused" : "Ready";
    els.status.textContent = label;
    els.statusPill.textContent = label;
    els.statusPill.classList.toggle("running", running);
  }

  function renderPseudocode() {
    const line = latestEvent ? latestEvent.line : -1;
    els.pseudocode.querySelectorAll("li").forEach((li) => li.classList.toggle("active-line", Number(li.dataset.line) === line));
  }

  function renderLog() {
    els.logCount.textContent = `${logEntries.length} event${logEntries.length === 1 ? "" : "s"}`;
    if (!logEntries.length) {
      const li = document.createElement("li"); li.className = "log-empty";
      li.textContent = "Your operations will appear here as you step through the algorithm.";
      els.log.replaceChildren(li); return;
    }
    const fragment = document.createDocumentFragment();
    logEntries.forEach((entry, index) => {
      const li = document.createElement("li");
      if (index === logEntries.length - 1) li.classList.add("latest");
      const step = document.createElement("span"); step.className = "log-step"; step.textContent = `#${entry.step}`;
      const text = document.createElement("span"); text.textContent = entry.description;
      li.append(step, text); fragment.append(li);
    });
    els.log.replaceChildren(fragment);
    els.log.scrollTop = els.log.scrollHeight;
  }

  function renderAll() {
    renderChart(); renderStats(); renderPseudocode();
  }

  function applyEvent(event) {
    current = event.array.slice();
    stats = { ...event.stats };
    sortedIndices = new Set(event.sorted);
    latestEvent = event;
    cursor++;
    logEntries.push({ step: cursor, description: event.description });
    renderAll();
    renderLog();
    if (cursor >= events.length) finish();
    else updateControls();
  }

  function finish() {
    stopPlayback();
    const sorted = current.every((value, index, array) => index === 0 || array[index - 1] <= value);
    if (!sorted) {
      els.status.textContent = "Error";
      els.statusPill.textContent = "Error";
      return;
    }
    sortedIndices = new Set(current.map((_, index) => index));
    els.completion.hidden = false;
    els.originalResult.textContent = `[${original.join(", ")}]`;
    els.sortedResult.textContent = `[${current.join(", ")}]`;
    renderAll();
    updateControls();
  }

  function stepForward() {
    if (running || cursor >= events.length) return;
    if (!events.length && !prepareRun()) return;
    if (cursor < events.length) applyEvent(events[cursor]);
  }

  function scheduleNext() {
    if (!running) return;
    if (cursor >= events.length) { finish(); return; }
    applyEvent(events[cursor]);
    if (running) timerId = setTimeout(scheduleNext, Number(els.speed.value));
  }

  function play() {
    if (running || cursor >= events.length) return;
    if (!events.length && !prepareRun()) return;
    running = true;
    updateControls();
    timerId = setTimeout(scheduleNext, 0);
  }

  function updateControls() {
    els.play.disabled = running || cursor >= events.length;
    els.pause.disabled = !running;
    els.step.disabled = running || cursor >= events.length;
    els.reset.disabled = !original.length;
    document.querySelectorAll(".algorithm-tab").forEach((button) => button.disabled = running);
  }

  $("#apply-btn").addEventListener("click", () => {
    const result = validateArray(els.input.value);
    if (result.error) { showError(result.error); return; }
    setArray(result.values);
  });
  els.input.addEventListener("keydown", (event) => {
    if (event.key === "Enter") $("#apply-btn").click();
  });
  $("#random-btn").addEventListener("click", () => {
    const length = 8 + Math.floor(Math.random() * 7);
    const values = Array.from({ length }, () => Math.floor(Math.random() * 41) - 10);
    setArray(values);
  });
  $("#sample-btn").addEventListener("click", () => setArray([5, 3, 8, 1, 2]));
  $("#clear-btn").addEventListener("click", clearLog);
  document.querySelectorAll(".algorithm-tab").forEach((button) => button.addEventListener("click", () => selectAlgorithm(button.dataset.algorithm)));
  els.play.addEventListener("click", play);
  els.pause.addEventListener("click", stopPlayback);
  els.step.addEventListener("click", stepForward);
  els.reset.addEventListener("click", () => prepareRun());
  els.speed.addEventListener("change", () => {
    if (running) {
      if (timerId !== null) clearTimeout(timerId);
      timerId = setTimeout(scheduleNext, Number(els.speed.value));
    }
  });

  // Keep browser history and rendering independent of algorithm generation.
  renderAlgorithmInfo();
  prepareRun();
})();