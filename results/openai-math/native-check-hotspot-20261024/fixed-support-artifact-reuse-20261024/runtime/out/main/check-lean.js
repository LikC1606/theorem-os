#!/usr/bin/env bun
var __create = Object.create;
var __defProp = Object.defineProperty;
var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
var __getOwnPropNames = Object.getOwnPropertyNames;
var __getProtoOf = Object.getPrototypeOf;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};
var __copyProps = (to, from, except, desc) => {
  if (from && typeof from === "object" || typeof from === "function") {
    for (let key of __getOwnPropNames(from))
      if (!__hasOwnProp.call(to, key) && key !== except)
        __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
  }
  return to;
};
var __toESM = (mod, isNodeMode, target) => (target = mod != null ? __create(__getProtoOf(mod)) : {}, __copyProps(
  // If the importer is in node compatibility mode or this is not an ESM
  // file that has been converted to a CommonJS file using a Babel-
  // compatible transform (i.e. "__esModule" has not been set), then set
  // "default" to the CommonJS "module.exports" for node compatibility.
  isNodeMode || !mod || !mod.__esModule ? __defProp(target, "default", { value: mod, enumerable: true }) : target,
  mod
));

// scripts/mathematics/checkLean.ts
var import_node_util = require("node:util");
var import_node_fs13 = __toESM(require("node:fs"));
var import_node_path14 = __toESM(require("node:path"));

// src/math/leanDiagnostics.ts
var import_node_fs10 = __toESM(require("node:fs"));
var import_node_path11 = __toESM(require("node:path"));

// src/math/mathProcess.ts
var import_node_crypto = __toESM(require("node:crypto"));
var import_node_child_process = require("node:child_process");
var import_node_path = __toESM(require("node:path"));
var import_node_string_decoder = require("node:string_decoder");
var MATH_PROCESS_OUTPUT_LIMIT = 12e3;
var PROCESS_STOP_GRACE_MS = 1e3;
function runLeanProcess(command, args, options) {
  const lock = (options.env ?? process.env).DEEPSCIENTIST_MATH_LEAN_LOCK;
  if (!lock) return runMathProcess(command, args, options);
  if (process.platform !== "linux" || !import_node_path.default.isAbsolute(lock)) throw new Error("math_lean_lock_requires_absolute_linux_path");
  const progress = options.onLockProgress ?? ((event) => console.error(JSON.stringify({ event, at: Date.now() })));
  if (!options.signal?.aborted) progress("lean_lock_waiting");
  const descriptor = 3 + (options.inheritedFds?.length ?? 0);
  return runMathProcess("/usr/bin/flock", [
    "--exclusive",
    lock,
    "/bin/sh",
    "-c",
    `printf 1 >&${descriptor}; exec "$@"`,
    "math-lean-lock",
    command,
    ...args
  ], {
    ...options,
    onExtraPipe: (stream) => stream.once("data", () => progress("lean_lock_acquired"))
  });
}
function limitMathOutput(value, limit = MATH_PROCESS_OUTPUT_LIMIT, capture = "tail") {
  if (Buffer.byteLength(value) <= limit) return value;
  const bytes = Buffer.from(value);
  if (capture === "head") return new import_node_string_decoder.StringDecoder("utf8").write(bytes.subarray(0, limit));
  let start = bytes.length - limit;
  while (start < bytes.length && (bytes[start] & 192) === 128) start++;
  return bytes.subarray(start).toString("utf8");
}
var stopMathProcess = (child, signal) => {
  if (process.platform !== "win32" && child.pid) {
    try {
      process.kill(-child.pid, signal);
      return;
    } catch {
    }
  }
  if (child.exitCode !== null || child.signalCode !== null) return;
  try {
    child.kill(signal);
  } catch {
  }
};
var runMathProcess = (command, args, options) => new Promise((resolve) => {
  const startedAt = Date.now();
  let child;
  let extraPipe;
  let stdout = Buffer.alloc(0), stderr = Buffer.alloc(0);
  const capture = (current, chunk) => {
    const bytes = typeof chunk === "string" ? Buffer.from(chunk) : chunk;
    const limit = options.outputLimit ?? MATH_PROCESS_OUTPUT_LIMIT;
    if (options.outputCapture === "head") return current.length >= limit ? current : Buffer.concat([current, bytes.subarray(0, limit - current.length)]);
    return Buffer.from(Buffer.concat([current, bytes]).subarray(-limit));
  };
  const decode = (bytes) => {
    let start = 0;
    if (options.outputCapture !== "head") while (start < bytes.length && (bytes[start] & 192) === 128) start++;
    return limitMathOutput(new import_node_string_decoder.StringDecoder("utf8").write(bytes.subarray(start)), options.outputLimit ?? MATH_PROCESS_OUTPUT_LIMIT, options.outputCapture);
  };
  const stdoutHash = import_node_crypto.default.createHash("sha256");
  const stderrHash = import_node_crypto.default.createHash("sha256");
  let timedOut = false;
  let aborted = options.signal?.aborted || false;
  let processError;
  let timeout;
  let forceStopTimeout;
  let fallbackTimeout;
  let settled = false;
  let started = false;
  let stopping = false;
  const finish = (exitCode, signal) => {
    if (settled) return;
    settled = true;
    if (stopping) stopMathProcess(child, "SIGKILL");
    if (timeout) clearTimeout(timeout);
    if (forceStopTimeout) clearTimeout(forceStopTimeout);
    if (fallbackTimeout) clearTimeout(fallbackTimeout);
    options.signal?.removeEventListener("abort", abort);
    resolve({
      started,
      exitCode,
      signal,
      stdout: decode(stdout),
      stderr: decode(stderr),
      stdoutSha256: stdoutHash.digest("hex"),
      stderrSha256: stderrHash.digest("hex"),
      timedOut,
      aborted,
      durationMs: Date.now() - startedAt,
      ...processError?.code ? { errorCode: processError.code } : {},
      ...processError?.message ? { errorMessage: processError.message } : {}
    });
  };
  const requestStop = () => {
    if (stopping || settled) return;
    stopping = true;
    stopMathProcess(child, options.stopGraceMs === 0 ? "SIGKILL" : "SIGTERM");
    forceStopTimeout = setTimeout(() => {
      stopMathProcess(child, "SIGKILL");
      fallbackTimeout = setTimeout(() => {
        child.stdin?.destroy();
        child.stdout?.destroy();
        child.stderr?.destroy();
        extraPipe?.destroy();
        finish(child.exitCode, child.signalCode);
      }, PROCESS_STOP_GRACE_MS);
    }, options.stopGraceMs ?? PROCESS_STOP_GRACE_MS);
  };
  const abort = () => {
    aborted = true;
    requestStop();
  };
  try {
    child = (0, import_node_child_process.spawn)(command, args, {
      cwd: options.cwd,
      env: options.env || process.env,
      detached: process.platform !== "win32",
      stdio: [
        options.stdin === void 0 && !options.onDuplexSpawn ? "ignore" : "pipe",
        "pipe",
        "pipe",
        ...options.inheritedFds ?? [],
        ...options.onExtraPipe ? ["pipe"] : []
      ]
    });
  } catch (error) {
    processError = error;
    finish(null, null);
    return;
  }
  child.stdout?.on("data", (chunk) => {
    if (settled) return;
    stdoutHash.update(chunk);
    stdout = capture(stdout, chunk);
  });
  child.stderr?.on("data", (chunk) => {
    if (settled) return;
    stderrHash.update(chunk);
    stderr = capture(stderr, chunk);
  });
  child.once("spawn", () => {
    started = true;
  });
  child.once("error", (error) => {
    processError = error;
  });
  child.stdin?.on("error", (error) => {
    if (error.code !== "EPIPE") processError = error;
  });
  child.once("close", (exitCode, signal) => finish(exitCode, signal));
  if (options.onExtraPipe) {
    extraPipe = child.stdio.at(-1);
    options.onExtraPipe(extraPipe);
  }
  if (options.stdin !== void 0) child.stdin?.end(options.stdin);
  options.signal?.addEventListener("abort", abort, { once: true });
  if (aborted) {
    requestStop();
    return;
  }
  if (options.onDuplexSpawn) {
    options.onDuplexSpawn(child);
    return;
  }
  if (Number.isFinite(options.timeoutMs)) timeout = setTimeout(() => {
    timedOut = true;
    requestStop();
  }, options.timeoutMs);
});

// src/math/mathConstructionSources.ts
var import_node_fs = __toESM(require("node:fs"));
var import_node_path2 = __toESM(require("node:path"));

// node_modules/smol-toml/dist/error.js
function getLineColFromPtr(string, ptr) {
  let lines = string.slice(0, ptr).split(/\r\n|\n|\r/g);
  return [lines.length, lines.pop().length + 1];
}
function makeCodeBlock(string, line, column) {
  let lines = string.split(/\r\n|\n|\r/g);
  let codeblock = "";
  let numberLen = (Math.log10(line + 1) | 0) + 1;
  for (let i = line - 1; i <= line + 1; i++) {
    let l = lines[i - 1];
    if (!l)
      continue;
    codeblock += i.toString().padEnd(numberLen, " ");
    codeblock += ":  ";
    codeblock += l;
    codeblock += "\n";
    if (i === line) {
      codeblock += " ".repeat(numberLen + column + 2);
      codeblock += "^\n";
    }
  }
  return codeblock;
}
var TomlError = class extends Error {
  line;
  column;
  codeblock;
  constructor(message, options) {
    const [line, column] = getLineColFromPtr(options.toml, options.ptr);
    const codeblock = makeCodeBlock(options.toml, line, column);
    super(`Invalid TOML document: ${message}

${codeblock}`, options);
    this.line = line;
    this.column = column;
    this.codeblock = codeblock;
  }
};

// node_modules/smol-toml/dist/util.js
function isEscaped(str, ptr) {
  let i = 0;
  while (str[ptr - ++i] === "\\")
    ;
  return --i && i % 2;
}
function indexOfNewline(str, start = 0, end = str.length) {
  let idx = str.indexOf("\n", start);
  if (str[idx - 1] === "\r")
    idx--;
  return idx <= end ? idx : -1;
}
function skipComment(str, ptr) {
  for (let i = ptr; i < str.length; i++) {
    let c = str[i];
    if (c === "\n")
      return i;
    if (c === "\r" && str[i + 1] === "\n")
      return i + 1;
    if (c < " " && c !== "	" || c === "\x7F") {
      throw new TomlError("control characters are not allowed in comments", {
        toml: str,
        ptr
      });
    }
  }
  return str.length;
}
function skipVoid(str, ptr, banNewLines, banComments) {
  let c;
  while (1) {
    while ((c = str[ptr]) === " " || c === "	" || !banNewLines && (c === "\n" || c === "\r" && str[ptr + 1] === "\n"))
      ptr++;
    if (banComments || c !== "#")
      break;
    ptr = skipComment(str, ptr);
  }
  return ptr;
}
function skipUntil(str, ptr, sep, end, banNewLines = false) {
  if (!end) {
    ptr = indexOfNewline(str, ptr);
    return ptr < 0 ? str.length : ptr;
  }
  for (let i = ptr; i < str.length; i++) {
    let c = str[i];
    if (c === "#") {
      i = indexOfNewline(str, i);
    } else if (c === sep) {
      return i + 1;
    } else if (c === end || banNewLines && (c === "\n" || c === "\r" && str[i + 1] === "\n")) {
      return i;
    }
  }
  throw new TomlError("cannot find end of structure", {
    toml: str,
    ptr
  });
}
function getStringEnd(str, seek) {
  let first = str[seek];
  let target = first === str[seek + 1] && str[seek + 1] === str[seek + 2] ? str.slice(seek, seek + 3) : first;
  seek += target.length - 1;
  do
    seek = str.indexOf(target, ++seek);
  while (seek > -1 && first !== "'" && isEscaped(str, seek));
  if (seek > -1) {
    seek += target.length;
    if (target.length > 1) {
      if (str[seek] === first)
        seek++;
      if (str[seek] === first)
        seek++;
    }
  }
  return seek;
}

// node_modules/smol-toml/dist/date.js
var DATE_TIME_RE = /^(\d{4}-\d{2}-\d{2})?[T ]?(?:(\d{2}):\d{2}(?::\d{2}(?:\.\d+)?)?)?(Z|[-+]\d{2}:\d{2})?$/i;
var TomlDate = class _TomlDate extends Date {
  #hasDate = false;
  #hasTime = false;
  #offset = null;
  constructor(date) {
    let hasDate = true;
    let hasTime = true;
    let offset = "Z";
    if (typeof date === "string") {
      let match = date.match(DATE_TIME_RE);
      if (match) {
        if (!match[1]) {
          hasDate = false;
          date = `0000-01-01T${date}`;
        }
        hasTime = !!match[2];
        hasTime && date[10] === " " && (date = date.replace(" ", "T"));
        if (match[2] && +match[2] > 23) {
          date = "";
        } else {
          offset = match[3] || null;
          date = date.toUpperCase();
          if (!offset && hasTime)
            date += "Z";
        }
      } else {
        date = "";
      }
    }
    super(date);
    if (!isNaN(this.getTime())) {
      this.#hasDate = hasDate;
      this.#hasTime = hasTime;
      this.#offset = offset;
    }
  }
  isDateTime() {
    return this.#hasDate && this.#hasTime;
  }
  isLocal() {
    return !this.#hasDate || !this.#hasTime || !this.#offset;
  }
  isDate() {
    return this.#hasDate && !this.#hasTime;
  }
  isTime() {
    return this.#hasTime && !this.#hasDate;
  }
  isValid() {
    return this.#hasDate || this.#hasTime;
  }
  toISOString() {
    let iso = super.toISOString();
    if (this.isDate())
      return iso.slice(0, 10);
    if (this.isTime())
      return iso.slice(11, 23);
    if (this.#offset === null)
      return iso.slice(0, -1);
    if (this.#offset === "Z")
      return iso;
    let offset = +this.#offset.slice(1, 3) * 60 + +this.#offset.slice(4, 6);
    offset = this.#offset[0] === "-" ? offset : -offset;
    let offsetDate = new Date(this.getTime() - offset * 6e4);
    return offsetDate.toISOString().slice(0, -1) + this.#offset;
  }
  static wrapAsOffsetDateTime(jsDate, offset = "Z") {
    let date = new _TomlDate(jsDate);
    date.#offset = offset;
    return date;
  }
  static wrapAsLocalDateTime(jsDate) {
    let date = new _TomlDate(jsDate);
    date.#offset = null;
    return date;
  }
  static wrapAsLocalDate(jsDate) {
    let date = new _TomlDate(jsDate);
    date.#hasTime = false;
    date.#offset = null;
    return date;
  }
  static wrapAsLocalTime(jsDate) {
    let date = new _TomlDate(jsDate);
    date.#hasDate = false;
    date.#offset = null;
    return date;
  }
};

// node_modules/smol-toml/dist/primitive.js
var INT_REGEX = /^((0x[0-9a-fA-F](_?[0-9a-fA-F])*)|(([+-]|0[ob])?\d(_?\d)*))$/;
var FLOAT_REGEX = /^[+-]?\d(_?\d)*(\.\d(_?\d)*)?([eE][+-]?\d(_?\d)*)?$/;
var LEADING_ZERO = /^[+-]?0[0-9_]/;
var ESCAPE_REGEX = /^[0-9a-f]{2,8}$/i;
var ESC_MAP = {
  b: "\b",
  t: "	",
  n: "\n",
  f: "\f",
  r: "\r",
  e: "\x1B",
  '"': '"',
  "\\": "\\"
};
function parseString(str, ptr = 0, endPtr = str.length) {
  let isLiteral = str[ptr] === "'";
  let isMultiline = str[ptr++] === str[ptr] && str[ptr] === str[ptr + 1];
  if (isMultiline) {
    endPtr -= 2;
    if (str[ptr += 2] === "\r")
      ptr++;
    if (str[ptr] === "\n")
      ptr++;
  }
  let tmp = 0;
  let isEscape;
  let parsed = "";
  let sliceStart = ptr;
  while (ptr < endPtr - 1) {
    let c = str[ptr++];
    if (c === "\n" || c === "\r" && str[ptr] === "\n") {
      if (!isMultiline) {
        throw new TomlError("newlines are not allowed in strings", {
          toml: str,
          ptr: ptr - 1
        });
      }
    } else if (c < " " && c !== "	" || c === "\x7F") {
      throw new TomlError("control characters are not allowed in strings", {
        toml: str,
        ptr: ptr - 1
      });
    }
    if (isEscape) {
      isEscape = false;
      if (c === "x" || c === "u" || c === "U") {
        let code = str.slice(ptr, ptr += c === "x" ? 2 : c === "u" ? 4 : 8);
        if (!ESCAPE_REGEX.test(code)) {
          throw new TomlError("invalid unicode escape", {
            toml: str,
            ptr: tmp
          });
        }
        try {
          parsed += String.fromCodePoint(parseInt(code, 16));
        } catch {
          throw new TomlError("invalid unicode escape", {
            toml: str,
            ptr: tmp
          });
        }
      } else if (isMultiline && (c === "\n" || c === " " || c === "	" || c === "\r")) {
        ptr = skipVoid(str, ptr - 1, true);
        if (str[ptr] !== "\n" && str[ptr] !== "\r") {
          throw new TomlError("invalid escape: only line-ending whitespace may be escaped", {
            toml: str,
            ptr: tmp
          });
        }
        ptr = skipVoid(str, ptr);
      } else if (c in ESC_MAP) {
        parsed += ESC_MAP[c];
      } else {
        throw new TomlError("unrecognized escape sequence", {
          toml: str,
          ptr: tmp
        });
      }
      sliceStart = ptr;
    } else if (!isLiteral && c === "\\") {
      tmp = ptr - 1;
      isEscape = true;
      parsed += str.slice(sliceStart, tmp);
    }
  }
  return parsed + str.slice(sliceStart, endPtr - 1);
}
function parseValue(value, toml, ptr, integersAsBigInt) {
  if (value === "true")
    return true;
  if (value === "false")
    return false;
  if (value === "-inf")
    return -Infinity;
  if (value === "inf" || value === "+inf")
    return Infinity;
  if (value === "nan" || value === "+nan" || value === "-nan")
    return NaN;
  if (value === "-0")
    return integersAsBigInt ? 0n : 0;
  let isInt = INT_REGEX.test(value);
  if (isInt || FLOAT_REGEX.test(value)) {
    if (LEADING_ZERO.test(value)) {
      throw new TomlError("leading zeroes are not allowed", {
        toml,
        ptr
      });
    }
    value = value.replace(/_/g, "");
    let numeric = +value;
    if (isNaN(numeric)) {
      throw new TomlError("invalid number", {
        toml,
        ptr
      });
    }
    if (isInt) {
      if ((isInt = !Number.isSafeInteger(numeric)) && !integersAsBigInt) {
        throw new TomlError("integer value cannot be represented losslessly", {
          toml,
          ptr
        });
      }
      if (isInt || integersAsBigInt === true)
        numeric = BigInt(value);
    }
    return numeric;
  }
  const date = new TomlDate(value);
  if (!date.isValid()) {
    throw new TomlError("invalid value", {
      toml,
      ptr
    });
  }
  return date;
}

// node_modules/smol-toml/dist/extract.js
function sliceAndTrimEndOf(str, startPtr, endPtr) {
  let value = str.slice(startPtr, endPtr);
  let commentIdx = value.indexOf("#");
  if (commentIdx > -1) {
    skipComment(str, commentIdx);
    value = value.slice(0, commentIdx);
  }
  return [value.trimEnd(), commentIdx];
}
function extractValue(str, ptr, end, depth, integersAsBigInt) {
  if (depth === 0) {
    throw new TomlError("document contains excessively nested structures. aborting.", {
      toml: str,
      ptr
    });
  }
  let c = str[ptr];
  if (c === "[" || c === "{") {
    let [value, endPtr2] = c === "[" ? parseArray(str, ptr, depth, integersAsBigInt) : parseInlineTable(str, ptr, depth, integersAsBigInt);
    if (end) {
      endPtr2 = skipVoid(str, endPtr2);
      if (str[endPtr2] === ",")
        endPtr2++;
      else if (str[endPtr2] !== end) {
        throw new TomlError("expected comma or end of structure", {
          toml: str,
          ptr: endPtr2
        });
      }
    }
    return [value, endPtr2];
  }
  let endPtr;
  if (c === '"' || c === "'") {
    endPtr = getStringEnd(str, ptr);
    let parsed = parseString(str, ptr, endPtr);
    if (end) {
      endPtr = skipVoid(str, endPtr);
      if (str[endPtr] && str[endPtr] !== "," && str[endPtr] !== end && str[endPtr] !== "\n" && str[endPtr] !== "\r") {
        throw new TomlError("unexpected character encountered", {
          toml: str,
          ptr: endPtr
        });
      }
      endPtr += +(str[endPtr] === ",");
    }
    return [parsed, endPtr];
  }
  endPtr = skipUntil(str, ptr, ",", end);
  let slice = sliceAndTrimEndOf(str, ptr, endPtr - +(str[endPtr - 1] === ","));
  if (!slice[0]) {
    throw new TomlError("incomplete key-value declaration: no value specified", {
      toml: str,
      ptr
    });
  }
  if (end && slice[1] > -1) {
    endPtr = skipVoid(str, ptr + slice[1]);
    endPtr += +(str[endPtr] === ",");
  }
  return [
    parseValue(slice[0], str, ptr, integersAsBigInt),
    endPtr
  ];
}

// node_modules/smol-toml/dist/struct.js
var KEY_PART_RE = /^[a-zA-Z0-9-_]+[ \t]*$/;
function parseKey(str, ptr, end = "=") {
  let dot = ptr - 1;
  let parsed = [];
  let endPtr = str.indexOf(end, ptr);
  if (endPtr < 0) {
    throw new TomlError("incomplete key-value: cannot find end of key", {
      toml: str,
      ptr
    });
  }
  do {
    let c = str[ptr = ++dot];
    if (c !== " " && c !== "	") {
      if (c === '"' || c === "'") {
        if (c === str[ptr + 1] && c === str[ptr + 2]) {
          throw new TomlError("multiline strings are not allowed in keys", {
            toml: str,
            ptr
          });
        }
        let eos = getStringEnd(str, ptr);
        if (eos < 0) {
          throw new TomlError("unfinished string encountered", {
            toml: str,
            ptr
          });
        }
        dot = str.indexOf(".", eos);
        let strEnd = str.slice(eos, dot < 0 || dot > endPtr ? endPtr : dot);
        let newLine = indexOfNewline(strEnd);
        if (newLine > -1) {
          throw new TomlError("newlines are not allowed in keys", {
            toml: str,
            ptr: ptr + dot + newLine
          });
        }
        if (strEnd.trimStart()) {
          throw new TomlError("found extra tokens after the string part", {
            toml: str,
            ptr: eos
          });
        }
        if (endPtr < eos) {
          endPtr = str.indexOf(end, eos);
          if (endPtr < 0) {
            throw new TomlError("incomplete key-value: cannot find end of key", {
              toml: str,
              ptr
            });
          }
        }
        parsed.push(parseString(str, ptr, eos));
      } else {
        dot = str.indexOf(".", ptr);
        let part = str.slice(ptr, dot < 0 || dot > endPtr ? endPtr : dot);
        if (!KEY_PART_RE.test(part)) {
          throw new TomlError("only letter, numbers, dashes and underscores are allowed in keys", {
            toml: str,
            ptr
          });
        }
        parsed.push(part.trimEnd());
      }
    }
  } while (dot + 1 && dot < endPtr);
  return [parsed, skipVoid(str, endPtr + 1, true, true)];
}
function parseInlineTable(str, ptr, depth, integersAsBigInt) {
  let res = {};
  let seen = /* @__PURE__ */ new Set();
  let c;
  ptr++;
  while ((c = str[ptr++]) !== "}" && c) {
    if (c === ",") {
      throw new TomlError("expected value, found comma", {
        toml: str,
        ptr: ptr - 1
      });
    } else if (c === "#")
      ptr = skipComment(str, ptr);
    else if (c !== " " && c !== "	" && c !== "\n" && c !== "\r") {
      let k;
      let t = res;
      let hasOwn = false;
      let [key, keyEndPtr] = parseKey(str, ptr - 1);
      for (let i = 0; i < key.length; i++) {
        if (i)
          t = hasOwn ? t[k] : t[k] = {};
        k = key[i];
        if ((hasOwn = Object.hasOwn(t, k)) && (typeof t[k] !== "object" || seen.has(t[k]))) {
          throw new TomlError("trying to redefine an already defined value", {
            toml: str,
            ptr
          });
        }
        if (!hasOwn && k === "__proto__") {
          Object.defineProperty(t, k, { enumerable: true, configurable: true, writable: true });
        }
      }
      if (hasOwn) {
        throw new TomlError("trying to redefine an already defined value", {
          toml: str,
          ptr
        });
      }
      let [value, valueEndPtr] = extractValue(str, keyEndPtr, "}", depth - 1, integersAsBigInt);
      seen.add(value);
      t[k] = value;
      ptr = valueEndPtr;
    }
  }
  if (!c) {
    throw new TomlError("unfinished table encountered", {
      toml: str,
      ptr
    });
  }
  return [res, ptr];
}
function parseArray(str, ptr, depth, integersAsBigInt) {
  let res = [];
  let c;
  ptr++;
  while ((c = str[ptr++]) !== "]" && c) {
    if (c === ",") {
      throw new TomlError("expected value, found comma", {
        toml: str,
        ptr: ptr - 1
      });
    } else if (c === "#")
      ptr = skipComment(str, ptr);
    else if (c !== " " && c !== "	" && c !== "\n" && c !== "\r") {
      let e = extractValue(str, ptr - 1, "]", depth - 1, integersAsBigInt);
      res.push(e[0]);
      ptr = e[1];
    }
  }
  if (!c) {
    throw new TomlError("unfinished array encountered", {
      toml: str,
      ptr
    });
  }
  return [res, ptr];
}

// node_modules/smol-toml/dist/parse.js
function peekTable(key, table, meta, type) {
  let t = table;
  let m = meta;
  let k;
  let hasOwn = false;
  let state;
  for (let i = 0; i < key.length; i++) {
    if (i) {
      t = hasOwn ? t[k] : t[k] = {};
      m = (state = m[k]).c;
      if (type === 0 && (state.t === 1 || state.t === 2)) {
        return null;
      }
      if (state.t === 2) {
        let l = t.length - 1;
        t = t[l];
        m = m[l].c;
      }
    }
    k = key[i];
    if ((hasOwn = Object.hasOwn(t, k)) && m[k]?.t === 0 && m[k]?.d) {
      return null;
    }
    if (!hasOwn) {
      if (k === "__proto__") {
        Object.defineProperty(t, k, { enumerable: true, configurable: true, writable: true });
        Object.defineProperty(m, k, { enumerable: true, configurable: true, writable: true });
      }
      m[k] = {
        t: i < key.length - 1 && type === 2 ? 3 : type,
        d: false,
        i: 0,
        c: {}
      };
    }
  }
  state = m[k];
  if (state.t !== type && !(type === 1 && state.t === 3)) {
    return null;
  }
  if (type === 2) {
    if (!state.d) {
      state.d = true;
      t[k] = [];
    }
    t[k].push(t = {});
    state.c[state.i++] = state = { t: 1, d: false, i: 0, c: {} };
  }
  if (state.d) {
    return null;
  }
  state.d = true;
  if (type === 1) {
    t = hasOwn ? t[k] : t[k] = {};
  } else if (type === 0 && hasOwn) {
    return null;
  }
  return [k, t, state.c];
}
function parse(toml, { maxDepth = 1e3, integersAsBigInt } = {}) {
  let res = {};
  let meta = {};
  let tbl = res;
  let m = meta;
  for (let ptr = skipVoid(toml, 0); ptr < toml.length; ) {
    if (toml[ptr] === "[") {
      let isTableArray = toml[++ptr] === "[";
      let k = parseKey(toml, ptr += +isTableArray, "]");
      if (isTableArray) {
        if (toml[k[1] - 1] !== "]") {
          throw new TomlError("expected end of table declaration", {
            toml,
            ptr: k[1] - 1
          });
        }
        k[1]++;
      }
      let p = peekTable(
        k[0],
        res,
        meta,
        isTableArray ? 2 : 1
        /* Type.EXPLICIT */
      );
      if (!p) {
        throw new TomlError("trying to redefine an already defined table or value", {
          toml,
          ptr
        });
      }
      m = p[2];
      tbl = p[1];
      ptr = k[1];
    } else {
      let k = parseKey(toml, ptr);
      let p = peekTable(
        k[0],
        tbl,
        m,
        0
        /* Type.DOTTED */
      );
      if (!p) {
        throw new TomlError("trying to redefine an already defined table or value", {
          toml,
          ptr
        });
      }
      let v = extractValue(toml, k[1], void 0, maxDepth, integersAsBigInt);
      p[1][p[0]] = v[0];
      ptr = v[1];
    }
    ptr = skipVoid(toml, ptr, true);
    if (toml[ptr] && toml[ptr] !== "\n" && toml[ptr] !== "\r") {
      throw new TomlError("each key-value declaration must be followed by an end-of-line", {
        toml,
        ptr
      });
    }
    ptr = skipVoid(toml, ptr);
  }
  return res;
}

// src/math/mathProofSourcePolicy.ts
var excludedSegments = /* @__PURE__ */ new Set([
  ".git",
  ".lake",
  "bench",
  "benchmark",
  "benchmarks",
  "build",
  "example",
  "examples",
  "lakefile",
  "private",
  "reference",
  "references",
  "solution",
  "solutions",
  "workspacetest",
  "test",
  "tests",
  "comparator",
  "comparators",
  "challenge",
  "challenges"
]);
function isAllowedMathProofSource(relative) {
  const normalized = relative.replaceAll("\\", "/");
  return normalized.endsWith(".lean") && !normalized.startsWith("/") && !/^[A-Za-z]:/u.test(normalized) && normalized.split("/").every(
    (part) => Boolean(part) && part !== "." && part !== ".." && !excludedSegments.has(part.replace(/\.lean$/iu, "").toLowerCase())
  );
}

// src/math/mathConstructionSources.ts
var LAKE_CONFIGURATION_FILES = [
  "lean-toolchain",
  "lakefile.toml",
  "lakefile.lean",
  "lake-manifest.json",
  ".lake/package-overrides.json"
];
function mathConstructionImports(source) {
  let offset = 0;
  const next = () => {
    for (; ; ) {
      while (/\s/u.test(source[offset] ?? "") && offset < source.length) offset++;
      if (source.startsWith("--", offset)) {
        const end = source.indexOf("\n", offset);
        offset = end < 0 ? source.length : end;
      } else if (source.startsWith("/-", offset)) {
        let depth = 1;
        offset += 2;
        while (offset < source.length && depth) {
          if (source.startsWith("/-", offset)) {
            depth++;
            offset += 2;
          } else if (source.startsWith("-/", offset)) {
            depth--;
            offset += 2;
          } else offset++;
        }
        if (depth) throw new Error("math_construction_unclosed_header_comment");
      } else break;
    }
    const token2 = source.slice(offset).match(/^(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»)(?:\.(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»))*/u)?.[0];
    if (token2) offset += token2.length;
    return token2;
  };
  const imports = [];
  const boundaries = /* @__PURE__ */ new Set([
    "import",
    "public",
    "private",
    "meta",
    "namespace",
    "section",
    "end",
    "theorem",
    "lemma",
    "def",
    "example",
    "abbrev",
    "opaque",
    "instance",
    "inductive",
    "structure",
    "class",
    "axiom",
    "constant",
    "variable",
    "universe",
    "open",
    "export",
    "set_option",
    "attribute",
    "noncomputable",
    "unsafe",
    "syntax",
    "macro",
    "elab",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "initialize",
    "builtin_initialize"
  ]);
  let token = next();
  while (token === "prelude" || token === "module") token = next();
  while (token === "import" || token === "public" || token === "private" || token === "meta") {
    while (token === "public" || token === "private" || token === "meta") token = next();
    if (token !== "import") break;
    token = next();
    if (!token || boundaries.has(token)) throw new Error("math_construction_invalid_import");
    while (token && !boundaries.has(token)) {
      imports.push(token);
      token = next();
    }
  }
  return imports;
}
var assertRegularSource = (root, relative) => {
  if (!isAllowedMathProofSource(relative)) throw new Error(`math_construction_source_excluded: ${relative}`);
  const file = import_node_path2.default.join(root, relative);
  if (import_node_fs.default.realpathSync(file) !== file || !import_node_fs.default.lstatSync(file).isFile())
    throw new Error("math_construction_source_path_invalid");
  return file;
};
function localSourceDirectories(root) {
  const directories = /* @__PURE__ */ new Set(["", "src"]);
  const config = import_node_path2.default.join(root, "lakefile.toml");
  if (import_node_fs.default.existsSync(config)) {
    if (import_node_fs.default.realpathSync(config) !== config || !import_node_fs.default.lstatSync(config).isFile())
      throw new Error("math_construction_config_path_invalid");
    const parsed = parse(import_node_fs.default.readFileSync(config, "utf8"));
    for (const library of Array.isArray(parsed.lean_lib) ? parsed.lean_lib : []) {
      if (library && typeof library === "object" && "srcDir" in library && typeof library.srcDir === "string") {
        const directory = library.srcDir;
        if (directory === ".") directories.add("");
        else if (!import_node_path2.default.isAbsolute(directory) && directory.split(/[\\/]/u).every((part) => part && part !== ".." && part !== "."))
          directories.add(directory);
        else throw new Error("math_construction_source_directory_invalid");
      }
    }
  }
  return directories;
}
var localModuleFile = (name) => {
  const parts = (name.match(/«[^»]+»|[^.]+/gu) ?? []).map((part) => part.replaceAll("\xAB", "").replaceAll("\xBB", ""));
  if (parts.some((part) => !part || part === "." || part === ".." || /[/\\\0]/u.test(part)))
    throw new Error("math_local_module_import_invalid");
  return `${parts.join("/")}.lean`;
};
var localImportFiles = (root, directories, moduleFile) => {
  return [...directories].map((directory) => ({ file: directory ? `${directory}/${moduleFile}` : moduleFile, sourceRoot: directory })).filter((candidate) => import_node_fs.default.existsSync(import_node_path2.default.join(root, candidate.file)));
};
function assertMathConstructionSources(rootInput, files) {
  for (const file of files)
    if (!isAllowedMathProofSource(file)) throw new Error(`math_construction_source_excluded: ${file}`);
  const root = import_node_fs.default.realpathSync(rootInput);
  const directories = localSourceDirectories(root);
  const queue = [...files];
  const visited = /* @__PURE__ */ new Set();
  for (let index = 0; index < queue.length; index++) {
    const relative = queue[index];
    if (visited.has(relative)) continue;
    visited.add(relative);
    const file = assertRegularSource(root, relative);
    const source = import_node_fs.default.readFileSync(file, "utf8");
    for (const name of mathConstructionImports(source)) {
      const moduleFile = localModuleFile(name);
      if (!isAllowedMathProofSource(moduleFile)) throw new Error(`math_construction_import_excluded: ${name}`);
      queue.push(...localImportFiles(root, directories, moduleFile).map((candidate) => candidate.file));
    }
  }
}
function mathLocalModuleBuildOrder(rootInput, input) {
  const root = import_node_fs.default.realpathSync(rootInput);
  const directories = [...localSourceDirectories(root)];
  const ordered = [];
  const visited = /* @__PURE__ */ new Set();
  const visiting = /* @__PURE__ */ new Set();
  const visit = (file, sourceRoot) => {
    if (visited.has(file)) return;
    if (visiting.has(file)) throw new Error("math_local_module_import_cycle");
    const absolute = import_node_path2.default.resolve(root, file);
    if (import_node_path2.default.relative(root, absolute).startsWith("..") || !file.endsWith(".lean") || import_node_fs.default.realpathSync(absolute) !== absolute || !import_node_fs.default.lstatSync(absolute).isFile())
      throw new Error("math_local_module_source_invalid");
    visiting.add(file);
    for (const name of mathConstructionImports(import_node_fs.default.readFileSync(absolute, "utf8"))) {
      const candidate = localImportFiles(root, directories, localModuleFile(name))[0];
      if (candidate) visit(candidate.file, candidate.sourceRoot);
    }
    visiting.delete(file);
    visited.add(file);
    ordered.push({
      file,
      sourceRoot: sourceRoot || ".",
      module: import_node_path2.default.posix.relative(sourceRoot || ".", file).replace(/\.lean$/u, "").replaceAll("/", ".")
    });
  };
  for (const relative of typeof input === "string" ? [input] : input) {
    const sourceRoot = directories.filter((directory) => directory && relative.startsWith(`${directory}/`)).sort((a, b) => b.length - a.length)[0] || "";
    visit(relative, sourceRoot);
  }
  return ordered;
}

// src/math/paths.ts
var import_node_fs2 = __toESM(require("node:fs"));
var import_node_path3 = __toESM(require("node:path"));
function repositoryRelativePath(value, normalize = false) {
  const relative = normalize ? value.replaceAll("\\", "/").replace(/^\.\//u, "") : value;
  if (!relative || /[\0\\]/u.test(relative) || relative.startsWith("/") || /^[A-Za-z]:/u.test(relative) || relative.split("/").some((part) => !part || part === "." || part === "..")) return void 0;
  return relative;
}
function assertMathCanonicalPath(target) {
  if (!import_node_path3.default.isAbsolute(target) || import_node_path3.default.resolve(target) !== target) throw new Error("math_path_invalid");
  let current = target;
  while (!import_node_fs2.default.existsSync(current)) {
    try {
      if (import_node_fs2.default.lstatSync(current).isSymbolicLink()) throw new Error("math_path_invalid");
    } catch (error) {
      if (error.code !== "ENOENT") throw error;
    }
    const parent = import_node_path3.default.dirname(current);
    if (parent === current) throw new Error("math_path_invalid");
    current = parent;
  }
  if (import_node_fs2.default.realpathSync(current) !== current) throw new Error("math_path_invalid");
}

// src/math/mathRuntimeIo.ts
var import_node_crypto2 = __toESM(require("node:crypto"));
var import_node_fs3 = __toESM(require("node:fs"));
var import_node_path4 = __toESM(require("node:path"));
var normalizeJson = (item, compare) => {
  if (Array.isArray(item)) return item.map((entry) => normalizeJson(entry, compare));
  if (item && typeof item === "object") {
    const prototype = Object.getPrototypeOf(item);
    if (prototype !== Object.prototype && prototype !== null) throw new Error("math_runtime_invalid_json");
    return Object.fromEntries(
      Object.entries(item).filter(([, entry]) => entry !== void 0).toSorted(([a], [b]) => compare(a, b)).map(([key, entry]) => [key, normalizeJson(entry, compare)])
    );
  }
  if (item === null || typeof item === "string" || typeof item === "boolean" || typeof item === "number" && Number.isFinite(item))
    return item;
  throw new Error("math_runtime_invalid_json");
};
function canonicalMathJson(value, compare = (a, b) => a < b ? -1 : a > b ? 1 : 0) {
  return JSON.stringify(normalizeJson(value, compare));
}
var mathDigest = (value) => import_node_crypto2.default.createHash("sha256").update(value).digest("hex");
var mathFileIdentity = (stat) => [stat.dev, stat.ino, stat.size, stat.mode, stat.mtimeNs, stat.ctimeNs].join(":");
var durableWrites = /* @__PURE__ */ new Map();
function syncMathDirectory(directory) {
  const descriptor = import_node_fs3.default.openSync(directory, import_node_fs3.default.constants.O_RDONLY | import_node_fs3.default.constants.O_DIRECTORY | import_node_fs3.default.constants.O_NOFOLLOW);
  try {
    import_node_fs3.default.fsyncSync(descriptor);
  } finally {
    import_node_fs3.default.closeSync(descriptor);
  }
}
function writeMathJsonDurable(file, value, mode = 384) {
  const contents = canonicalMathJson(value), digest3 = mathDigest(contents);
  const previous = durableWrites.get(file);
  if (previous?.digest === digest3 && previous.mode === mode) {
    try {
      if (mathFileIdentity(import_node_fs3.default.lstatSync(file, { bigint: true })) === previous.identity) return;
    } catch {
    }
  }
  const temporary = `${file}.${import_node_crypto2.default.randomUUID()}.tmp`;
  const descriptor = import_node_fs3.default.openSync(
    temporary,
    import_node_fs3.default.constants.O_CREAT | import_node_fs3.default.constants.O_EXCL | import_node_fs3.default.constants.O_WRONLY | import_node_fs3.default.constants.O_NOFOLLOW,
    384
  );
  try {
    import_node_fs3.default.writeFileSync(descriptor, contents, "utf8");
    import_node_fs3.default.fchmodSync(descriptor, mode);
    import_node_fs3.default.fsyncSync(descriptor);
  } finally {
    import_node_fs3.default.closeSync(descriptor);
  }
  import_node_fs3.default.renameSync(temporary, file);
  syncMathDirectory(import_node_path4.default.dirname(file));
  if (durableWrites.size >= 128) durableWrites.delete(durableWrites.keys().next().value);
  durableWrites.set(file, { digest: digest3, mode, identity: mathFileIdentity(import_node_fs3.default.lstatSync(file, { bigint: true })) });
}
function readMathFile(file, maxBytes = Infinity, options = {}) {
  const descriptor = import_node_fs3.default.openSync(file, import_node_fs3.default.constants.O_RDONLY | import_node_fs3.default.constants.O_NOFOLLOW | import_node_fs3.default.constants.O_NONBLOCK);
  try {
    const before = import_node_fs3.default.fstatSync(descriptor, { bigint: true });
    if (!before.isFile() || before.nlink !== BigInt(1)) throw new Error("math_runtime_integrity");
    if (!options.headOnly && before.size > maxBytes) throw new Error("math_runtime_file_too_large");
    let bytes;
    if (Number.isFinite(maxBytes)) {
      bytes = Buffer.alloc(Math.min(Number(before.size), maxBytes) + (options.headOnly ? 0 : 1));
      let size = 0, read;
      while ((read = import_node_fs3.default.readSync(descriptor, bytes, size, bytes.length - size, null)) > 0) size += read;
      if (!options.headOnly && size > maxBytes) throw new Error("math_runtime_file_too_large");
      bytes = bytes.subarray(0, size);
    } else bytes = import_node_fs3.default.readFileSync(descriptor);
    const after = import_node_fs3.default.fstatSync(descriptor, { bigint: true });
    const current = import_node_fs3.default.lstatSync(file, { bigint: true });
    if (mathFileIdentity(before) !== mathFileIdentity(after) || mathFileIdentity(before) !== mathFileIdentity(current) || current.nlink !== BigInt(1))
      throw new Error("math_runtime_integrity");
    return { bytes, identity: mathFileIdentity(before), truncated: before.size > bytes.length };
  } finally {
    import_node_fs3.default.closeSync(descriptor);
  }
}
function readMathText(file, maxBytes = Infinity, options = {}) {
  const { bytes, truncated } = readMathFile(file, maxBytes, options);
  return new TextDecoder("utf-8", { fatal: true }).decode(bytes, { stream: Boolean(options.headOnly && truncated) });
}
var readMathJson = (file) => JSON.parse(readMathText(file));

// src/math/leanSyntax.ts
function maskLeanCommentsAndStrings(source) {
  return maskLeanText(source, true);
}
var leanScopeCommands = (cleaned) => cleaned.matchAll(
  /^[ \t]*(?:(?:noncomputable|public|private|meta)[ \t]+)*(namespace|section|end|variable|open)(?:[ \t]+([^\n]*))?[ \t]*\r?$/gmu
);
function updateLeanScopes(scopes, kind, name = "") {
  if (kind === "namespace" || kind === "section") scopes.push({ kind, name });
  else if (kind === "end") scopes.pop();
}
var leanScopeNamespace = (scopes) => scopes.filter((scope) => scope.kind === "namespace").map((scope) => scope.name).join(".");
function maskLeanText(source, maskStrings) {
  const chunks = [];
  let visibleStart = 0;
  let hiddenStart = -1;
  let blockDepth = 0;
  let lineComment = false;
  let quote = false;
  let escaped = false;
  const beginHidden = (index) => {
    chunks.push(source.slice(visibleStart, index));
    hiddenStart = index;
  };
  const endHidden = (index) => {
    chunks.push(source.slice(hiddenStart, index).replace(/[^\r\n]+/g, (text) => " ".repeat(text.length)));
    visibleStart = index;
    hiddenStart = -1;
  };
  for (let index = 0; index < source.length; index++) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === "\n") {
        lineComment = false;
        endHidden(index + 1);
      }
    } else if (blockDepth) {
      if (current === "/" && next === "-") {
        blockDepth++;
        index++;
      } else if (current === "-" && next === "/") {
        if (--blockDepth === 0) endHidden(index + 2);
        index++;
      }
    } else if (quote) {
      if (escaped) escaped = false;
      else if (current === "\\") escaped = true;
      else if (current === '"') {
        quote = false;
        if (maskStrings) endHidden(index + 1);
      }
    } else if (current === "-" && next === "-") {
      beginHidden(index);
      lineComment = true;
      index++;
    } else if (current === "/" && next === "-") {
      beginHidden(index);
      blockDepth = 1;
      index++;
    } else if (current === '"') {
      if (maskStrings) beginHidden(index);
      quote = true;
    }
  }
  if (hiddenStart >= 0) endHidden(source.length);
  chunks.push(source.slice(visibleStart));
  return chunks.join("");
}

// src/math/leanSource.ts
var isLeanNameCharacter = (value) => Boolean(value && /[\p{L}\p{M}\p{N}_'.]/u.test(value));
function inspectScopedLeanDeclarations(source) {
  const scopes = [], commands = leanScopeCommands(maskLeanCommentsAndStrings(source));
  let command = commands.next();
  return inspectLeanDeclarations(source).map((declaration) => {
    while (!command.done && command.value.index < declaration.startOffset) {
      updateLeanScopes(scopes, command.value[1], command.value[2]?.trim());
      command = commands.next();
    }
    const namespace = leanScopeNamespace(scopes);
    const qualifiedName = declaration.name.startsWith("_root_.") ? declaration.name.slice(7) : [namespace, declaration.name].filter(Boolean).join(".");
    return { ...declaration, namespace, qualifiedName };
  });
}
function leanDeclarationContextCommands(source, theoremName) {
  const declarations = inspectScopedLeanDeclarations(source);
  const target = declarations.find((declaration) => declaration.qualifiedName === theoremName) ?? declarations.find((declaration) => declaration.name === theoremName);
  if (!target) throw new Error("Lean type query declaration was not found.");
  const regions = inspectLeanDeclarationRegions(source);
  const frames = [[]];
  const ends = [];
  for (const command of leanScopeCommands(maskLeanCommentsAndStrings(source))) {
    if (command.index >= target.startOffset) break;
    if (regions.some((region) => command.index >= region.startOffset && command.index < region.endOffset)) continue;
    const kind = command[1];
    if (kind === "namespace" || kind === "section") {
      frames.push([command[0].trim()]);
      ends.push(`end${command[2]?.trim() ? " " + command[2].trim() : ""}`);
    } else if (kind === "end") {
      if (frames.length > 1) {
        frames.pop();
        ends.pop();
      }
    } else if (kind === "open") frames.at(-1).push(command[0].trim());
  }
  return { before: frames.flat(), after: ends.reverse() };
}
function* leanSourceDeclarations(source) {
  const declarationKeywords = {
    t: "theorem",
    l: "lemma",
    d: "def",
    i: "instance",
    o: "opaque",
    a: "abbrev"
  };
  const codePointBefore = (offset) => {
    if (offset <= 0) return void 0;
    const previous = source.charCodeAt(offset - 1);
    if (previous >= 56320 && previous <= 57343 && offset >= 2) return source.slice(offset - 2, offset);
    return source[offset - 1];
  };
  const codePointAt = (offset) => {
    if (offset >= source.length) return void 0;
    const value = source.codePointAt(offset);
    return value === void 0 ? void 0 : String.fromCodePoint(value);
  };
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let quote;
  let escaped = false;
  const skipTrivia = (start) => {
    let cursor = start;
    while (cursor < source.length) {
      if (/\s/u.test(source[cursor])) {
        cursor += 1;
        continue;
      }
      if (source[cursor] === "-" && source[cursor + 1] === "-") {
        cursor += 2;
        while (cursor < source.length && source[cursor] !== "\n") cursor += 1;
        continue;
      }
      if (source[cursor] === "/" && source[cursor + 1] === "-") {
        cursor += 2;
        let depth = 1;
        while (cursor < source.length && depth > 0) {
          if (source[cursor] === "/" && source[cursor + 1] === "-") {
            depth += 1;
            cursor += 2;
          } else if (source[cursor] === "-" && source[cursor + 1] === "/") {
            depth -= 1;
            cursor += 2;
          } else cursor += 1;
        }
        continue;
      }
      break;
    }
    return cursor;
  };
  const hasEquationArrow = (start) => {
    let cursor = start + 1;
    const delimiters = [];
    while (cursor < source.length) {
      cursor = skipTrivia(cursor);
      const value = source[cursor];
      if (value === void 0) break;
      if (value === '"') {
        cursor++;
        while (cursor < source.length) {
          if (source[cursor] === "\\") cursor += 2;
          else if (source[cursor++] === '"') break;
        }
        continue;
      }
      if (value === "'" && !isLeanNameCharacter(codePointBefore(cursor))) {
        const character = /^'(?:\\(?:u\{[\da-fA-F]+\}|u[\da-fA-F]{4}|x[\da-fA-F]{2}|[^\r\n])|[^'\\\r\n])'/u.exec(source.slice(cursor));
        if (character) {
          cursor += character[0].length;
          continue;
        }
      }
      if (delimiters.length === 0) {
        if (source.startsWith("=>", cursor)) return true;
        if (source.startsWith(":=", cursor)) return false;
        if (/[=→≤≥≠∧∨↔∈∉]/u.test(value) || source.startsWith("->", cursor)) return false;
        if (!isLeanNameCharacter(codePointBefore(cursor)) && /^(?:fun|λ|match)(?![\p{L}\p{M}\p{N}_'.])/u.test(source.slice(cursor))) return false;
      }
      const opening = "([{".indexOf(value);
      if (opening >= 0) delimiters.push(")]}"[opening]);
      else if (")]}".includes(value) && delimiters.pop() !== value) return false;
      cursor++;
    }
    return false;
  };
  const canonicalize = (value) => {
    let result2 = "";
    let cursor = 0;
    let nestedBlockDepth = 0;
    let inLineComment = false;
    let stringQuote;
    let stringEscaped = false;
    let pendingSpace = false;
    while (cursor < value.length) {
      const current = value[cursor];
      const next = value[cursor + 1];
      if (inLineComment) {
        if (current === "\n") {
          inLineComment = false;
          pendingSpace = true;
        }
        cursor += 1;
        continue;
      }
      if (nestedBlockDepth > 0) {
        if (current === "/" && next === "-") {
          nestedBlockDepth += 1;
          cursor += 2;
        } else if (current === "-" && next === "/") {
          nestedBlockDepth -= 1;
          cursor += 2;
          pendingSpace = true;
        } else cursor += 1;
        continue;
      }
      if (stringQuote) {
        if (pendingSpace && result2) result2 += " ";
        pendingSpace = false;
        result2 += current;
        if (stringEscaped) stringEscaped = false;
        else if (current === "\\") stringEscaped = true;
        else if (current === stringQuote) stringQuote = void 0;
        cursor += 1;
        continue;
      }
      if (current === "-" && next === "-") {
        inLineComment = true;
        cursor += 2;
        continue;
      }
      if (current === "/" && next === "-") {
        nestedBlockDepth = 1;
        cursor += 2;
        continue;
      }
      if (current === '"') {
        if (pendingSpace && result2) result2 += " ";
        pendingSpace = false;
        stringQuote = current;
        result2 += current;
      } else if (/\s/u.test(current)) {
        pendingSpace = true;
      } else {
        if (pendingSpace && result2) result2 += " ";
        pendingSpace = false;
        result2 += current;
      }
      cursor += 1;
    }
    return result2.trim();
  };
  while (index < source.length) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === "\n") lineComment = false;
      index += 1;
      continue;
    }
    if (blockDepth > 0) {
      if (current === "/" && next === "-") {
        blockDepth += 1;
        index += 2;
      } else if (current === "-" && next === "/") {
        blockDepth -= 1;
        index += 2;
      } else index += 1;
      continue;
    }
    if (quote) {
      if (escaped) escaped = false;
      else if (current === "\\") escaped = true;
      else if (current === quote) quote = void 0;
      index += 1;
      continue;
    }
    if (current === "-" && next === "-") {
      lineComment = true;
      index += 2;
      continue;
    }
    if (current === "/" && next === "-") {
      blockDepth = 1;
      index += 2;
      continue;
    }
    if (current === '"') {
      quote = current;
      index += 1;
      continue;
    }
    const keyword = declarationKeywords[current];
    if (!keyword || !source.startsWith(keyword, index) || isLeanNameCharacter(codePointBefore(index)) || isLeanNameCharacter(codePointAt(index + keyword.length))) {
      index += 1;
      continue;
    }
    const nameStart = skipTrivia(index + keyword.length);
    const name = /^[\p{L}\p{M}\p{N}_']+(?:\.[\p{L}\p{M}\p{N}_']+)*/u.exec(source.slice(nameStart))?.[0] ?? "";
    const nameEnd = nameStart + name.length;
    if (!name) {
      index += keyword.length;
      continue;
    }
    let cursor = nameEnd;
    let parenDepth = 0;
    let bracketDepth = 0;
    let braceDepth = 0;
    let localBlockDepth = 0;
    let localLineComment = false;
    let localQuote;
    let localEscaped = false;
    let proofStart = -1;
    let bodyOffset = -1;
    let hasTopLevelMatchType = false;
    let pendingLocalBindings = 0;
    while (cursor < source.length) {
      const value = source[cursor];
      const following = source[cursor + 1];
      if (localLineComment) {
        if (value === "\n") localLineComment = false;
        cursor += 1;
        continue;
      }
      if (localBlockDepth > 0) {
        if (value === "/" && following === "-") {
          localBlockDepth += 1;
          cursor += 2;
        } else if (value === "-" && following === "/") {
          localBlockDepth -= 1;
          cursor += 2;
        } else cursor += 1;
        continue;
      }
      if (localQuote) {
        if (localEscaped) localEscaped = false;
        else if (value === "\\") localEscaped = true;
        else if (value === localQuote) localQuote = void 0;
        cursor += 1;
        continue;
      }
      if (value === "-" && following === "-") {
        localLineComment = true;
        cursor += 2;
        continue;
      }
      if (value === "/" && following === "-") {
        localBlockDepth = 1;
        cursor += 2;
        continue;
      }
      if (value === '"') {
        localQuote = value;
        cursor += 1;
        continue;
      }
      if (parenDepth === 0 && bracketDepth === 0 && braceDepth === 0 && !isLeanNameCharacter(codePointBefore(cursor))) {
        const binding = /^(?:letI|haveI|let|have)\b/u.exec(source.slice(cursor));
        if (binding && !isLeanNameCharacter(codePointAt(cursor + binding[0].length))) {
          pendingLocalBindings++;
          cursor += binding[0].length;
          continue;
        }
      }
      if (parenDepth === 0 && bracketDepth === 0 && braceDepth === 0 && source.startsWith("match", cursor) && !isLeanNameCharacter(codePointBefore(cursor)) && !isLeanNameCharacter(codePointAt(cursor + 5)))
        hasTopLevelMatchType = true;
      if (value === "(") parenDepth += 1;
      else if (value === ")") parenDepth = Math.max(0, parenDepth - 1);
      else if (value === "[") bracketDepth += 1;
      else if (value === "]") bracketDepth = Math.max(0, bracketDepth - 1);
      else if (value === "{") braceDepth += 1;
      else if (value === "}") braceDepth = Math.max(0, braceDepth - 1);
      else if (value === ":" && following === "=" && parenDepth === 0 && bracketDepth === 0 && braceDepth === 0) {
        if (pendingLocalBindings > 0) {
          pendingLocalBindings--;
          cursor += 2;
          continue;
        }
        proofStart = cursor;
        bodyOffset = cursor + 2;
        break;
      } else if (value === "|" && !hasTopLevelMatchType && following !== "|" && following !== ">" && parenDepth === 0 && bracketDepth === 0 && braceDepth === 0 && /^\s*$/u.test(source.slice(source.lastIndexOf("\n", cursor - 1) + 1, cursor)) && hasEquationArrow(cursor)) {
        proofStart = cursor;
        bodyOffset = cursor;
        break;
      }
      cursor += 1;
    }
    if (proofStart >= 0) {
      const startOffset = index;
      index = Math.max(bodyOffset, proofStart + 1);
      const header = source.slice(nameStart, proofStart);
      yield Object.freeze({
        startOffset,
        bodyOffset,
        name,
        kind: keyword === "theorem" || keyword === "lemma" ? "theorem" : keyword === "instance" ? "instance" : "definition",
        get canonicalHeader() {
          return canonicalize(header);
        }
      });
    } else index = nameEnd;
  }
}
var leanSourceDeclarationCache = /* @__PURE__ */ new Map();
var LEAN_SOURCE_DECLARATION_CACHE_MAX_ENTRIES = 128;
var cachedLeanSourceDeclarations = (source) => {
  const key = mathDigest(source);
  const cached = leanSourceDeclarationCache.get(key);
  if (cached) {
    leanSourceDeclarationCache.delete(key);
    leanSourceDeclarationCache.set(key, cached);
    return cached;
  }
  const declarations = Object.freeze([...leanSourceDeclarations(source)]);
  leanSourceDeclarationCache.set(key, declarations);
  while (leanSourceDeclarationCache.size > LEAN_SOURCE_DECLARATION_CACHE_MAX_ENTRIES) {
    const oldest = leanSourceDeclarationCache.keys().next().value;
    if (oldest === void 0) break;
    leanSourceDeclarationCache.delete(oldest);
  }
  return declarations;
};
var inspectLeanDeclarations = (source) => Object.freeze(
  [...cachedLeanSourceDeclarations(source)].map(
    ({ startOffset, name, kind, canonicalHeader }) => Object.freeze({ startOffset, name, kind, declarationType: canonicalHeader })
  )
);
var inspectLeanDeclarationRegions = (source) => [...cachedLeanSourceDeclarations(source)].map((declaration) => {
  const lineStart = source.lastIndexOf("\n", declaration.startOffset - 1) + 1;
  const indentation = source.slice(lineStart, declaration.startOffset).match(/^\s*/u)?.[0].length ?? 0;
  let endOffset = source.length;
  let cursor = source.indexOf("\n", declaration.bodyOffset);
  while (cursor >= 0 && cursor + 1 < source.length) {
    const start = cursor + 1;
    const end = source.indexOf("\n", start);
    const line = source.slice(start, end < 0 ? void 0 : end);
    if (line.trim() && !line.trimStart().startsWith("--") && (line.match(/^\s*/u)?.[0].length ?? 0) <= indentation) {
      endOffset = start;
      break;
    }
    cursor = end;
  }
  return {
    name: declaration.name,
    startOffset: declaration.startOffset,
    declarationType: declaration.canonicalHeader,
    bodyOffset: declaration.bodyOffset,
    endOffset
  };
});

// src/math/mathProofEnvironment.ts
var import_node_fs5 = __toESM(require("node:fs"));
var import_node_path6 = __toESM(require("node:path"));
var import_node_net = __toESM(require("node:net"));

// node_modules/zod/v3/external.js
var external_exports = {};
__export(external_exports, {
  BRAND: () => BRAND,
  DIRTY: () => DIRTY,
  EMPTY_PATH: () => EMPTY_PATH,
  INVALID: () => INVALID,
  NEVER: () => NEVER,
  OK: () => OK,
  ParseStatus: () => ParseStatus,
  Schema: () => ZodType,
  ZodAny: () => ZodAny,
  ZodArray: () => ZodArray,
  ZodBigInt: () => ZodBigInt,
  ZodBoolean: () => ZodBoolean,
  ZodBranded: () => ZodBranded,
  ZodCatch: () => ZodCatch,
  ZodDate: () => ZodDate,
  ZodDefault: () => ZodDefault,
  ZodDiscriminatedUnion: () => ZodDiscriminatedUnion,
  ZodEffects: () => ZodEffects,
  ZodEnum: () => ZodEnum,
  ZodError: () => ZodError,
  ZodFirstPartyTypeKind: () => ZodFirstPartyTypeKind,
  ZodFunction: () => ZodFunction,
  ZodIntersection: () => ZodIntersection,
  ZodIssueCode: () => ZodIssueCode,
  ZodLazy: () => ZodLazy,
  ZodLiteral: () => ZodLiteral,
  ZodMap: () => ZodMap,
  ZodNaN: () => ZodNaN,
  ZodNativeEnum: () => ZodNativeEnum,
  ZodNever: () => ZodNever,
  ZodNull: () => ZodNull,
  ZodNullable: () => ZodNullable,
  ZodNumber: () => ZodNumber,
  ZodObject: () => ZodObject,
  ZodOptional: () => ZodOptional,
  ZodParsedType: () => ZodParsedType,
  ZodPipeline: () => ZodPipeline,
  ZodPromise: () => ZodPromise,
  ZodReadonly: () => ZodReadonly,
  ZodRecord: () => ZodRecord,
  ZodSchema: () => ZodType,
  ZodSet: () => ZodSet,
  ZodString: () => ZodString,
  ZodSymbol: () => ZodSymbol,
  ZodTransformer: () => ZodEffects,
  ZodTuple: () => ZodTuple,
  ZodType: () => ZodType,
  ZodUndefined: () => ZodUndefined,
  ZodUnion: () => ZodUnion,
  ZodUnknown: () => ZodUnknown,
  ZodVoid: () => ZodVoid,
  addIssueToContext: () => addIssueToContext,
  any: () => anyType,
  array: () => arrayType,
  bigint: () => bigIntType,
  boolean: () => booleanType,
  coerce: () => coerce,
  custom: () => custom,
  date: () => dateType,
  datetimeRegex: () => datetimeRegex,
  defaultErrorMap: () => en_default,
  discriminatedUnion: () => discriminatedUnionType,
  effect: () => effectsType,
  enum: () => enumType,
  function: () => functionType,
  getErrorMap: () => getErrorMap,
  getParsedType: () => getParsedType,
  instanceof: () => instanceOfType,
  intersection: () => intersectionType,
  isAborted: () => isAborted,
  isAsync: () => isAsync,
  isDirty: () => isDirty,
  isValid: () => isValid,
  late: () => late,
  lazy: () => lazyType,
  literal: () => literalType,
  makeIssue: () => makeIssue,
  map: () => mapType,
  nan: () => nanType,
  nativeEnum: () => nativeEnumType,
  never: () => neverType,
  null: () => nullType,
  nullable: () => nullableType,
  number: () => numberType,
  object: () => objectType,
  objectUtil: () => objectUtil,
  oboolean: () => oboolean,
  onumber: () => onumber,
  optional: () => optionalType,
  ostring: () => ostring,
  pipeline: () => pipelineType,
  preprocess: () => preprocessType,
  promise: () => promiseType,
  quotelessJson: () => quotelessJson,
  record: () => recordType,
  set: () => setType,
  setErrorMap: () => setErrorMap,
  strictObject: () => strictObjectType,
  string: () => stringType,
  symbol: () => symbolType,
  transformer: () => effectsType,
  tuple: () => tupleType,
  undefined: () => undefinedType,
  union: () => unionType,
  unknown: () => unknownType,
  util: () => util,
  void: () => voidType
});

// node_modules/zod/v3/helpers/util.js
var util;
(function(util2) {
  util2.assertEqual = (_) => {
  };
  function assertIs(_arg) {
  }
  util2.assertIs = assertIs;
  function assertNever(_x) {
    throw new Error();
  }
  util2.assertNever = assertNever;
  util2.arrayToEnum = (items) => {
    const obj = {};
    for (const item of items) {
      obj[item] = item;
    }
    return obj;
  };
  util2.getValidEnumValues = (obj) => {
    const validKeys = util2.objectKeys(obj).filter((k) => typeof obj[obj[k]] !== "number");
    const filtered = {};
    for (const k of validKeys) {
      filtered[k] = obj[k];
    }
    return util2.objectValues(filtered);
  };
  util2.objectValues = (obj) => {
    return util2.objectKeys(obj).map(function(e) {
      return obj[e];
    });
  };
  util2.objectKeys = typeof Object.keys === "function" ? (obj) => Object.keys(obj) : (object) => {
    const keys = [];
    for (const key in object) {
      if (Object.prototype.hasOwnProperty.call(object, key)) {
        keys.push(key);
      }
    }
    return keys;
  };
  util2.find = (arr, checker) => {
    for (const item of arr) {
      if (checker(item))
        return item;
    }
    return void 0;
  };
  util2.isInteger = typeof Number.isInteger === "function" ? (val) => Number.isInteger(val) : (val) => typeof val === "number" && Number.isFinite(val) && Math.floor(val) === val;
  function joinValues(array, separator = " | ") {
    return array.map((val) => typeof val === "string" ? `'${val}'` : val).join(separator);
  }
  util2.joinValues = joinValues;
  util2.jsonStringifyReplacer = (_, value) => {
    if (typeof value === "bigint") {
      return value.toString();
    }
    return value;
  };
})(util || (util = {}));
var objectUtil;
(function(objectUtil2) {
  objectUtil2.mergeShapes = (first, second) => {
    return {
      ...first,
      ...second
      // second overwrites first
    };
  };
})(objectUtil || (objectUtil = {}));
var ZodParsedType = util.arrayToEnum([
  "string",
  "nan",
  "number",
  "integer",
  "float",
  "boolean",
  "date",
  "bigint",
  "symbol",
  "function",
  "undefined",
  "null",
  "array",
  "object",
  "unknown",
  "promise",
  "void",
  "never",
  "map",
  "set"
]);
var getParsedType = (data) => {
  const t = typeof data;
  switch (t) {
    case "undefined":
      return ZodParsedType.undefined;
    case "string":
      return ZodParsedType.string;
    case "number":
      return Number.isNaN(data) ? ZodParsedType.nan : ZodParsedType.number;
    case "boolean":
      return ZodParsedType.boolean;
    case "function":
      return ZodParsedType.function;
    case "bigint":
      return ZodParsedType.bigint;
    case "symbol":
      return ZodParsedType.symbol;
    case "object":
      if (Array.isArray(data)) {
        return ZodParsedType.array;
      }
      if (data === null) {
        return ZodParsedType.null;
      }
      if (data.then && typeof data.then === "function" && data.catch && typeof data.catch === "function") {
        return ZodParsedType.promise;
      }
      if (typeof Map !== "undefined" && data instanceof Map) {
        return ZodParsedType.map;
      }
      if (typeof Set !== "undefined" && data instanceof Set) {
        return ZodParsedType.set;
      }
      if (typeof Date !== "undefined" && data instanceof Date) {
        return ZodParsedType.date;
      }
      return ZodParsedType.object;
    default:
      return ZodParsedType.unknown;
  }
};

// node_modules/zod/v3/ZodError.js
var ZodIssueCode = util.arrayToEnum([
  "invalid_type",
  "invalid_literal",
  "custom",
  "invalid_union",
  "invalid_union_discriminator",
  "invalid_enum_value",
  "unrecognized_keys",
  "invalid_arguments",
  "invalid_return_type",
  "invalid_date",
  "invalid_string",
  "too_small",
  "too_big",
  "invalid_intersection_types",
  "not_multiple_of",
  "not_finite"
]);
var quotelessJson = (obj) => {
  const json = JSON.stringify(obj, null, 2);
  return json.replace(/"([^"]+)":/g, "$1:");
};
var ZodError = class _ZodError extends Error {
  get errors() {
    return this.issues;
  }
  constructor(issues) {
    super();
    this.issues = [];
    this.addIssue = (sub) => {
      this.issues = [...this.issues, sub];
    };
    this.addIssues = (subs = []) => {
      this.issues = [...this.issues, ...subs];
    };
    const actualProto = new.target.prototype;
    if (Object.setPrototypeOf) {
      Object.setPrototypeOf(this, actualProto);
    } else {
      this.__proto__ = actualProto;
    }
    this.name = "ZodError";
    this.issues = issues;
  }
  format(_mapper) {
    const mapper = _mapper || function(issue) {
      return issue.message;
    };
    const fieldErrors = { _errors: [] };
    const processError = (error) => {
      for (const issue of error.issues) {
        if (issue.code === "invalid_union") {
          issue.unionErrors.map(processError);
        } else if (issue.code === "invalid_return_type") {
          processError(issue.returnTypeError);
        } else if (issue.code === "invalid_arguments") {
          processError(issue.argumentsError);
        } else if (issue.path.length === 0) {
          fieldErrors._errors.push(mapper(issue));
        } else {
          let curr = fieldErrors;
          let i = 0;
          while (i < issue.path.length) {
            const el = issue.path[i];
            const terminal = i === issue.path.length - 1;
            if (!terminal) {
              curr[el] = curr[el] || { _errors: [] };
            } else {
              curr[el] = curr[el] || { _errors: [] };
              curr[el]._errors.push(mapper(issue));
            }
            curr = curr[el];
            i++;
          }
        }
      }
    };
    processError(this);
    return fieldErrors;
  }
  static assert(value) {
    if (!(value instanceof _ZodError)) {
      throw new Error(`Not a ZodError: ${value}`);
    }
  }
  toString() {
    return this.message;
  }
  get message() {
    return JSON.stringify(this.issues, util.jsonStringifyReplacer, 2);
  }
  get isEmpty() {
    return this.issues.length === 0;
  }
  flatten(mapper = (issue) => issue.message) {
    const fieldErrors = {};
    const formErrors = [];
    for (const sub of this.issues) {
      if (sub.path.length > 0) {
        const firstEl = sub.path[0];
        fieldErrors[firstEl] = fieldErrors[firstEl] || [];
        fieldErrors[firstEl].push(mapper(sub));
      } else {
        formErrors.push(mapper(sub));
      }
    }
    return { formErrors, fieldErrors };
  }
  get formErrors() {
    return this.flatten();
  }
};
ZodError.create = (issues) => {
  const error = new ZodError(issues);
  return error;
};

// node_modules/zod/v3/locales/en.js
var errorMap = (issue, _ctx) => {
  let message;
  switch (issue.code) {
    case ZodIssueCode.invalid_type:
      if (issue.received === ZodParsedType.undefined) {
        message = "Required";
      } else {
        message = `Expected ${issue.expected}, received ${issue.received}`;
      }
      break;
    case ZodIssueCode.invalid_literal:
      message = `Invalid literal value, expected ${JSON.stringify(issue.expected, util.jsonStringifyReplacer)}`;
      break;
    case ZodIssueCode.unrecognized_keys:
      message = `Unrecognized key(s) in object: ${util.joinValues(issue.keys, ", ")}`;
      break;
    case ZodIssueCode.invalid_union:
      message = `Invalid input`;
      break;
    case ZodIssueCode.invalid_union_discriminator:
      message = `Invalid discriminator value. Expected ${util.joinValues(issue.options)}`;
      break;
    case ZodIssueCode.invalid_enum_value:
      message = `Invalid enum value. Expected ${util.joinValues(issue.options)}, received '${issue.received}'`;
      break;
    case ZodIssueCode.invalid_arguments:
      message = `Invalid function arguments`;
      break;
    case ZodIssueCode.invalid_return_type:
      message = `Invalid function return type`;
      break;
    case ZodIssueCode.invalid_date:
      message = `Invalid date`;
      break;
    case ZodIssueCode.invalid_string:
      if (typeof issue.validation === "object") {
        if ("includes" in issue.validation) {
          message = `Invalid input: must include "${issue.validation.includes}"`;
          if (typeof issue.validation.position === "number") {
            message = `${message} at one or more positions greater than or equal to ${issue.validation.position}`;
          }
        } else if ("startsWith" in issue.validation) {
          message = `Invalid input: must start with "${issue.validation.startsWith}"`;
        } else if ("endsWith" in issue.validation) {
          message = `Invalid input: must end with "${issue.validation.endsWith}"`;
        } else {
          util.assertNever(issue.validation);
        }
      } else if (issue.validation !== "regex") {
        message = `Invalid ${issue.validation}`;
      } else {
        message = "Invalid";
      }
      break;
    case ZodIssueCode.too_small:
      if (issue.type === "array")
        message = `Array must contain ${issue.exact ? "exactly" : issue.inclusive ? `at least` : `more than`} ${issue.minimum} element(s)`;
      else if (issue.type === "string")
        message = `String must contain ${issue.exact ? "exactly" : issue.inclusive ? `at least` : `over`} ${issue.minimum} character(s)`;
      else if (issue.type === "number")
        message = `Number must be ${issue.exact ? `exactly equal to ` : issue.inclusive ? `greater than or equal to ` : `greater than `}${issue.minimum}`;
      else if (issue.type === "bigint")
        message = `Number must be ${issue.exact ? `exactly equal to ` : issue.inclusive ? `greater than or equal to ` : `greater than `}${issue.minimum}`;
      else if (issue.type === "date")
        message = `Date must be ${issue.exact ? `exactly equal to ` : issue.inclusive ? `greater than or equal to ` : `greater than `}${new Date(Number(issue.minimum))}`;
      else
        message = "Invalid input";
      break;
    case ZodIssueCode.too_big:
      if (issue.type === "array")
        message = `Array must contain ${issue.exact ? `exactly` : issue.inclusive ? `at most` : `less than`} ${issue.maximum} element(s)`;
      else if (issue.type === "string")
        message = `String must contain ${issue.exact ? `exactly` : issue.inclusive ? `at most` : `under`} ${issue.maximum} character(s)`;
      else if (issue.type === "number")
        message = `Number must be ${issue.exact ? `exactly` : issue.inclusive ? `less than or equal to` : `less than`} ${issue.maximum}`;
      else if (issue.type === "bigint")
        message = `BigInt must be ${issue.exact ? `exactly` : issue.inclusive ? `less than or equal to` : `less than`} ${issue.maximum}`;
      else if (issue.type === "date")
        message = `Date must be ${issue.exact ? `exactly` : issue.inclusive ? `smaller than or equal to` : `smaller than`} ${new Date(Number(issue.maximum))}`;
      else
        message = "Invalid input";
      break;
    case ZodIssueCode.custom:
      message = `Invalid input`;
      break;
    case ZodIssueCode.invalid_intersection_types:
      message = `Intersection results could not be merged`;
      break;
    case ZodIssueCode.not_multiple_of:
      message = `Number must be a multiple of ${issue.multipleOf}`;
      break;
    case ZodIssueCode.not_finite:
      message = "Number must be finite";
      break;
    default:
      message = _ctx.defaultError;
      util.assertNever(issue);
  }
  return { message };
};
var en_default = errorMap;

// node_modules/zod/v3/errors.js
var overrideErrorMap = en_default;
function setErrorMap(map) {
  overrideErrorMap = map;
}
function getErrorMap() {
  return overrideErrorMap;
}

// node_modules/zod/v3/helpers/parseUtil.js
var makeIssue = (params) => {
  const { data, path: path15, errorMaps, issueData } = params;
  const fullPath = [...path15, ...issueData.path || []];
  const fullIssue = {
    ...issueData,
    path: fullPath
  };
  if (issueData.message !== void 0) {
    return {
      ...issueData,
      path: fullPath,
      message: issueData.message
    };
  }
  let errorMessage = "";
  const maps = errorMaps.filter((m) => !!m).slice().reverse();
  for (const map of maps) {
    errorMessage = map(fullIssue, { data, defaultError: errorMessage }).message;
  }
  return {
    ...issueData,
    path: fullPath,
    message: errorMessage
  };
};
var EMPTY_PATH = [];
function addIssueToContext(ctx, issueData) {
  const overrideMap = getErrorMap();
  const issue = makeIssue({
    issueData,
    data: ctx.data,
    path: ctx.path,
    errorMaps: [
      ctx.common.contextualErrorMap,
      // contextual error map is first priority
      ctx.schemaErrorMap,
      // then schema-bound map if available
      overrideMap,
      // then global override map
      overrideMap === en_default ? void 0 : en_default
      // then global default map
    ].filter((x) => !!x)
  });
  ctx.common.issues.push(issue);
}
var ParseStatus = class _ParseStatus {
  constructor() {
    this.value = "valid";
  }
  dirty() {
    if (this.value === "valid")
      this.value = "dirty";
  }
  abort() {
    if (this.value !== "aborted")
      this.value = "aborted";
  }
  static mergeArray(status, results) {
    const arrayValue = [];
    for (const s of results) {
      if (s.status === "aborted")
        return INVALID;
      if (s.status === "dirty")
        status.dirty();
      arrayValue.push(s.value);
    }
    return { status: status.value, value: arrayValue };
  }
  static async mergeObjectAsync(status, pairs) {
    const syncPairs = [];
    for (const pair of pairs) {
      const key = await pair.key;
      const value = await pair.value;
      syncPairs.push({
        key,
        value
      });
    }
    return _ParseStatus.mergeObjectSync(status, syncPairs);
  }
  static mergeObjectSync(status, pairs) {
    const finalObject = {};
    for (const pair of pairs) {
      const { key, value } = pair;
      if (key.status === "aborted")
        return INVALID;
      if (value.status === "aborted")
        return INVALID;
      if (key.status === "dirty")
        status.dirty();
      if (value.status === "dirty")
        status.dirty();
      if (key.value !== "__proto__" && (typeof value.value !== "undefined" || pair.alwaysSet)) {
        finalObject[key.value] = value.value;
      }
    }
    return { status: status.value, value: finalObject };
  }
};
var INVALID = Object.freeze({
  status: "aborted"
});
var DIRTY = (value) => ({ status: "dirty", value });
var OK = (value) => ({ status: "valid", value });
var isAborted = (x) => x.status === "aborted";
var isDirty = (x) => x.status === "dirty";
var isValid = (x) => x.status === "valid";
var isAsync = (x) => typeof Promise !== "undefined" && x instanceof Promise;

// node_modules/zod/v3/helpers/errorUtil.js
var errorUtil;
(function(errorUtil2) {
  errorUtil2.errToObj = (message) => typeof message === "string" ? { message } : message || {};
  errorUtil2.toString = (message) => typeof message === "string" ? message : message?.message;
})(errorUtil || (errorUtil = {}));

// node_modules/zod/v3/types.js
var ParseInputLazyPath = class {
  constructor(parent, value, path15, key) {
    this._cachedPath = [];
    this.parent = parent;
    this.data = value;
    this._path = path15;
    this._key = key;
  }
  get path() {
    if (!this._cachedPath.length) {
      if (Array.isArray(this._key)) {
        this._cachedPath.push(...this._path, ...this._key);
      } else {
        this._cachedPath.push(...this._path, this._key);
      }
    }
    return this._cachedPath;
  }
};
var handleResult = (ctx, result2) => {
  if (isValid(result2)) {
    return { success: true, data: result2.value };
  } else {
    if (!ctx.common.issues.length) {
      throw new Error("Validation failed but no issues detected.");
    }
    return {
      success: false,
      get error() {
        if (this._error)
          return this._error;
        const error = new ZodError(ctx.common.issues);
        this._error = error;
        return this._error;
      }
    };
  }
};
function processCreateParams(params) {
  if (!params)
    return {};
  const { errorMap: errorMap2, invalid_type_error, required_error, description } = params;
  if (errorMap2 && (invalid_type_error || required_error)) {
    throw new Error(`Can't use "invalid_type_error" or "required_error" in conjunction with custom error map.`);
  }
  if (errorMap2)
    return { errorMap: errorMap2, description };
  const customMap = (iss, ctx) => {
    const { message } = params;
    if (iss.code === "invalid_enum_value") {
      return { message: message ?? ctx.defaultError };
    }
    if (typeof ctx.data === "undefined") {
      return { message: message ?? required_error ?? ctx.defaultError };
    }
    if (iss.code !== "invalid_type")
      return { message: ctx.defaultError };
    return { message: message ?? invalid_type_error ?? ctx.defaultError };
  };
  return { errorMap: customMap, description };
}
var ZodType = class {
  get description() {
    return this._def.description;
  }
  _getType(input) {
    return getParsedType(input.data);
  }
  _getOrReturnCtx(input, ctx) {
    return ctx || {
      common: input.parent.common,
      data: input.data,
      parsedType: getParsedType(input.data),
      schemaErrorMap: this._def.errorMap,
      path: input.path,
      parent: input.parent
    };
  }
  _processInputParams(input) {
    return {
      status: new ParseStatus(),
      ctx: {
        common: input.parent.common,
        data: input.data,
        parsedType: getParsedType(input.data),
        schemaErrorMap: this._def.errorMap,
        path: input.path,
        parent: input.parent
      }
    };
  }
  _parseSync(input) {
    const result2 = this._parse(input);
    if (isAsync(result2)) {
      throw new Error("Synchronous parse encountered promise.");
    }
    return result2;
  }
  _parseAsync(input) {
    const result2 = this._parse(input);
    return Promise.resolve(result2);
  }
  parse(data, params) {
    const result2 = this.safeParse(data, params);
    if (result2.success)
      return result2.data;
    throw result2.error;
  }
  safeParse(data, params) {
    const ctx = {
      common: {
        issues: [],
        async: params?.async ?? false,
        contextualErrorMap: params?.errorMap
      },
      path: params?.path || [],
      schemaErrorMap: this._def.errorMap,
      parent: null,
      data,
      parsedType: getParsedType(data)
    };
    const result2 = this._parseSync({ data, path: ctx.path, parent: ctx });
    return handleResult(ctx, result2);
  }
  "~validate"(data) {
    const ctx = {
      common: {
        issues: [],
        async: !!this["~standard"].async
      },
      path: [],
      schemaErrorMap: this._def.errorMap,
      parent: null,
      data,
      parsedType: getParsedType(data)
    };
    if (!this["~standard"].async) {
      try {
        const result2 = this._parseSync({ data, path: [], parent: ctx });
        return isValid(result2) ? {
          value: result2.value
        } : {
          issues: ctx.common.issues
        };
      } catch (err) {
        if (err?.message?.toLowerCase()?.includes("encountered")) {
          this["~standard"].async = true;
        }
        ctx.common = {
          issues: [],
          async: true
        };
      }
    }
    return this._parseAsync({ data, path: [], parent: ctx }).then((result2) => isValid(result2) ? {
      value: result2.value
    } : {
      issues: ctx.common.issues
    });
  }
  async parseAsync(data, params) {
    const result2 = await this.safeParseAsync(data, params);
    if (result2.success)
      return result2.data;
    throw result2.error;
  }
  async safeParseAsync(data, params) {
    const ctx = {
      common: {
        issues: [],
        contextualErrorMap: params?.errorMap,
        async: true
      },
      path: params?.path || [],
      schemaErrorMap: this._def.errorMap,
      parent: null,
      data,
      parsedType: getParsedType(data)
    };
    const maybeAsyncResult = this._parse({ data, path: ctx.path, parent: ctx });
    const result2 = await (isAsync(maybeAsyncResult) ? maybeAsyncResult : Promise.resolve(maybeAsyncResult));
    return handleResult(ctx, result2);
  }
  refine(check, message) {
    const getIssueProperties = (val) => {
      if (typeof message === "string" || typeof message === "undefined") {
        return { message };
      } else if (typeof message === "function") {
        return message(val);
      } else {
        return message;
      }
    };
    return this._refinement((val, ctx) => {
      const result2 = check(val);
      const setError = () => ctx.addIssue({
        code: ZodIssueCode.custom,
        ...getIssueProperties(val)
      });
      if (typeof Promise !== "undefined" && result2 instanceof Promise) {
        return result2.then((data) => {
          if (!data) {
            setError();
            return false;
          } else {
            return true;
          }
        });
      }
      if (!result2) {
        setError();
        return false;
      } else {
        return true;
      }
    });
  }
  refinement(check, refinementData) {
    return this._refinement((val, ctx) => {
      if (!check(val)) {
        ctx.addIssue(typeof refinementData === "function" ? refinementData(val, ctx) : refinementData);
        return false;
      } else {
        return true;
      }
    });
  }
  _refinement(refinement) {
    return new ZodEffects({
      schema: this,
      typeName: ZodFirstPartyTypeKind.ZodEffects,
      effect: { type: "refinement", refinement }
    });
  }
  superRefine(refinement) {
    return this._refinement(refinement);
  }
  constructor(def) {
    this.spa = this.safeParseAsync;
    this._def = def;
    this.parse = this.parse.bind(this);
    this.safeParse = this.safeParse.bind(this);
    this.parseAsync = this.parseAsync.bind(this);
    this.safeParseAsync = this.safeParseAsync.bind(this);
    this.spa = this.spa.bind(this);
    this.refine = this.refine.bind(this);
    this.refinement = this.refinement.bind(this);
    this.superRefine = this.superRefine.bind(this);
    this.optional = this.optional.bind(this);
    this.nullable = this.nullable.bind(this);
    this.nullish = this.nullish.bind(this);
    this.array = this.array.bind(this);
    this.promise = this.promise.bind(this);
    this.or = this.or.bind(this);
    this.and = this.and.bind(this);
    this.transform = this.transform.bind(this);
    this.brand = this.brand.bind(this);
    this.default = this.default.bind(this);
    this.catch = this.catch.bind(this);
    this.describe = this.describe.bind(this);
    this.pipe = this.pipe.bind(this);
    this.readonly = this.readonly.bind(this);
    this.isNullable = this.isNullable.bind(this);
    this.isOptional = this.isOptional.bind(this);
    this["~standard"] = {
      version: 1,
      vendor: "zod",
      validate: (data) => this["~validate"](data)
    };
  }
  optional() {
    return ZodOptional.create(this, this._def);
  }
  nullable() {
    return ZodNullable.create(this, this._def);
  }
  nullish() {
    return this.nullable().optional();
  }
  array() {
    return ZodArray.create(this);
  }
  promise() {
    return ZodPromise.create(this, this._def);
  }
  or(option) {
    return ZodUnion.create([this, option], this._def);
  }
  and(incoming) {
    return ZodIntersection.create(this, incoming, this._def);
  }
  transform(transform) {
    return new ZodEffects({
      ...processCreateParams(this._def),
      schema: this,
      typeName: ZodFirstPartyTypeKind.ZodEffects,
      effect: { type: "transform", transform }
    });
  }
  default(def) {
    const defaultValueFunc = typeof def === "function" ? def : () => def;
    return new ZodDefault({
      ...processCreateParams(this._def),
      innerType: this,
      defaultValue: defaultValueFunc,
      typeName: ZodFirstPartyTypeKind.ZodDefault
    });
  }
  brand() {
    return new ZodBranded({
      typeName: ZodFirstPartyTypeKind.ZodBranded,
      type: this,
      ...processCreateParams(this._def)
    });
  }
  catch(def) {
    const catchValueFunc = typeof def === "function" ? def : () => def;
    return new ZodCatch({
      ...processCreateParams(this._def),
      innerType: this,
      catchValue: catchValueFunc,
      typeName: ZodFirstPartyTypeKind.ZodCatch
    });
  }
  describe(description) {
    const This = this.constructor;
    return new This({
      ...this._def,
      description
    });
  }
  pipe(target) {
    return ZodPipeline.create(this, target);
  }
  readonly() {
    return ZodReadonly.create(this);
  }
  isOptional() {
    return this.safeParse(void 0).success;
  }
  isNullable() {
    return this.safeParse(null).success;
  }
};
var cuidRegex = /^c[^\s-]{8,}$/i;
var cuid2Regex = /^[0-9a-z]+$/;
var ulidRegex = /^[0-9A-HJKMNP-TV-Z]{26}$/i;
var uuidRegex = /^[0-9a-fA-F]{8}\b-[0-9a-fA-F]{4}\b-[0-9a-fA-F]{4}\b-[0-9a-fA-F]{4}\b-[0-9a-fA-F]{12}$/i;
var nanoidRegex = /^[a-z0-9_-]{21}$/i;
var jwtRegex = /^[A-Za-z0-9-_]+\.[A-Za-z0-9-_]+\.[A-Za-z0-9-_]*$/;
var durationRegex = /^[-+]?P(?!$)(?:(?:[-+]?\d+Y)|(?:[-+]?\d+[.,]\d+Y$))?(?:(?:[-+]?\d+M)|(?:[-+]?\d+[.,]\d+M$))?(?:(?:[-+]?\d+W)|(?:[-+]?\d+[.,]\d+W$))?(?:(?:[-+]?\d+D)|(?:[-+]?\d+[.,]\d+D$))?(?:T(?=[\d+-])(?:(?:[-+]?\d+H)|(?:[-+]?\d+[.,]\d+H$))?(?:(?:[-+]?\d+M)|(?:[-+]?\d+[.,]\d+M$))?(?:[-+]?\d+(?:[.,]\d+)?S)?)??$/;
var emailRegex = /^(?!\.)(?!.*\.\.)([A-Z0-9_'+\-\.]*)[A-Z0-9_+-]@([A-Z0-9][A-Z0-9\-]*\.)+[A-Z]{2,}$/i;
var _emojiRegex = `^(\\p{Extended_Pictographic}|\\p{Emoji_Component})+$`;
var emojiRegex;
var ipv4Regex = /^(?:(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.){3}(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])$/;
var ipv4CidrRegex = /^(?:(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.){3}(?:25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\/(3[0-2]|[12]?[0-9])$/;
var ipv6Regex = /^(([0-9a-fA-F]{1,4}:){7,7}[0-9a-fA-F]{1,4}|([0-9a-fA-F]{1,4}:){1,7}:|([0-9a-fA-F]{1,4}:){1,6}:[0-9a-fA-F]{1,4}|([0-9a-fA-F]{1,4}:){1,5}(:[0-9a-fA-F]{1,4}){1,2}|([0-9a-fA-F]{1,4}:){1,4}(:[0-9a-fA-F]{1,4}){1,3}|([0-9a-fA-F]{1,4}:){1,3}(:[0-9a-fA-F]{1,4}){1,4}|([0-9a-fA-F]{1,4}:){1,2}(:[0-9a-fA-F]{1,4}){1,5}|[0-9a-fA-F]{1,4}:((:[0-9a-fA-F]{1,4}){1,6})|:((:[0-9a-fA-F]{1,4}){1,7}|:)|fe80:(:[0-9a-fA-F]{0,4}){0,4}%[0-9a-zA-Z]{1,}|::(ffff(:0{1,4}){0,1}:){0,1}((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}(25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])|([0-9a-fA-F]{1,4}:){1,4}:((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}(25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9]))$/;
var ipv6CidrRegex = /^(([0-9a-fA-F]{1,4}:){7,7}[0-9a-fA-F]{1,4}|([0-9a-fA-F]{1,4}:){1,7}:|([0-9a-fA-F]{1,4}:){1,6}:[0-9a-fA-F]{1,4}|([0-9a-fA-F]{1,4}:){1,5}(:[0-9a-fA-F]{1,4}){1,2}|([0-9a-fA-F]{1,4}:){1,4}(:[0-9a-fA-F]{1,4}){1,3}|([0-9a-fA-F]{1,4}:){1,3}(:[0-9a-fA-F]{1,4}){1,4}|([0-9a-fA-F]{1,4}:){1,2}(:[0-9a-fA-F]{1,4}){1,5}|[0-9a-fA-F]{1,4}:((:[0-9a-fA-F]{1,4}){1,6})|:((:[0-9a-fA-F]{1,4}){1,7}|:)|fe80:(:[0-9a-fA-F]{0,4}){0,4}%[0-9a-zA-Z]{1,}|::(ffff(:0{1,4}){0,1}:){0,1}((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}(25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])|([0-9a-fA-F]{1,4}:){1,4}:((25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9])\.){3,3}(25[0-5]|(2[0-4]|1{0,1}[0-9]){0,1}[0-9]))\/(12[0-8]|1[01][0-9]|[1-9]?[0-9])$/;
var base64Regex = /^([0-9a-zA-Z+/]{4})*(([0-9a-zA-Z+/]{2}==)|([0-9a-zA-Z+/]{3}=))?$/;
var base64urlRegex = /^([0-9a-zA-Z-_]{4})*(([0-9a-zA-Z-_]{2}(==)?)|([0-9a-zA-Z-_]{3}(=)?))?$/;
var dateRegexSource = `((\\d\\d[2468][048]|\\d\\d[13579][26]|\\d\\d0[48]|[02468][048]00|[13579][26]00)-02-29|\\d{4}-((0[13578]|1[02])-(0[1-9]|[12]\\d|3[01])|(0[469]|11)-(0[1-9]|[12]\\d|30)|(02)-(0[1-9]|1\\d|2[0-8])))`;
var dateRegex = new RegExp(`^${dateRegexSource}$`);
function timeRegexSource(args) {
  let secondsRegexSource = `[0-5]\\d`;
  if (args.precision) {
    secondsRegexSource = `${secondsRegexSource}\\.\\d{${args.precision}}`;
  } else if (args.precision == null) {
    secondsRegexSource = `${secondsRegexSource}(\\.\\d+)?`;
  }
  const secondsQuantifier = args.precision ? "+" : "?";
  return `([01]\\d|2[0-3]):[0-5]\\d(:${secondsRegexSource})${secondsQuantifier}`;
}
function timeRegex(args) {
  return new RegExp(`^${timeRegexSource(args)}$`);
}
function datetimeRegex(args) {
  let regex = `${dateRegexSource}T${timeRegexSource(args)}`;
  const opts = [];
  opts.push(args.local ? `Z?` : `Z`);
  if (args.offset)
    opts.push(`([+-]\\d{2}:?\\d{2})`);
  regex = `${regex}(${opts.join("|")})`;
  return new RegExp(`^${regex}$`);
}
function isValidIP(ip, version) {
  if ((version === "v4" || !version) && ipv4Regex.test(ip)) {
    return true;
  }
  if ((version === "v6" || !version) && ipv6Regex.test(ip)) {
    return true;
  }
  return false;
}
function isValidJWT(jwt, alg) {
  if (!jwtRegex.test(jwt))
    return false;
  try {
    const [header] = jwt.split(".");
    if (!header)
      return false;
    const base64 = header.replace(/-/g, "+").replace(/_/g, "/").padEnd(header.length + (4 - header.length % 4) % 4, "=");
    const decoded = JSON.parse(atob(base64));
    if (typeof decoded !== "object" || decoded === null)
      return false;
    if ("typ" in decoded && decoded?.typ !== "JWT")
      return false;
    if (!decoded.alg)
      return false;
    if (alg && decoded.alg !== alg)
      return false;
    return true;
  } catch {
    return false;
  }
}
function isValidCidr(ip, version) {
  if ((version === "v4" || !version) && ipv4CidrRegex.test(ip)) {
    return true;
  }
  if ((version === "v6" || !version) && ipv6CidrRegex.test(ip)) {
    return true;
  }
  return false;
}
var ZodString = class _ZodString extends ZodType {
  _parse(input) {
    if (this._def.coerce) {
      input.data = String(input.data);
    }
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.string) {
      const ctx2 = this._getOrReturnCtx(input);
      addIssueToContext(ctx2, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.string,
        received: ctx2.parsedType
      });
      return INVALID;
    }
    const status = new ParseStatus();
    let ctx = void 0;
    for (const check of this._def.checks) {
      if (check.kind === "min") {
        if (input.data.length < check.value) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_small,
            minimum: check.value,
            type: "string",
            inclusive: true,
            exact: false,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "max") {
        if (input.data.length > check.value) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_big,
            maximum: check.value,
            type: "string",
            inclusive: true,
            exact: false,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "length") {
        const tooBig = input.data.length > check.value;
        const tooSmall = input.data.length < check.value;
        if (tooBig || tooSmall) {
          ctx = this._getOrReturnCtx(input, ctx);
          if (tooBig) {
            addIssueToContext(ctx, {
              code: ZodIssueCode.too_big,
              maximum: check.value,
              type: "string",
              inclusive: true,
              exact: true,
              message: check.message
            });
          } else if (tooSmall) {
            addIssueToContext(ctx, {
              code: ZodIssueCode.too_small,
              minimum: check.value,
              type: "string",
              inclusive: true,
              exact: true,
              message: check.message
            });
          }
          status.dirty();
        }
      } else if (check.kind === "email") {
        if (!emailRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "email",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "emoji") {
        if (!emojiRegex) {
          emojiRegex = new RegExp(_emojiRegex, "u");
        }
        if (!emojiRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "emoji",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "uuid") {
        if (!uuidRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "uuid",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "nanoid") {
        if (!nanoidRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "nanoid",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "cuid") {
        if (!cuidRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "cuid",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "cuid2") {
        if (!cuid2Regex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "cuid2",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "ulid") {
        if (!ulidRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "ulid",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "url") {
        try {
          new URL(input.data);
        } catch {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "url",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "regex") {
        check.regex.lastIndex = 0;
        const testResult = check.regex.test(input.data);
        if (!testResult) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "regex",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "trim") {
        input.data = input.data.trim();
      } else if (check.kind === "includes") {
        if (!input.data.includes(check.value, check.position)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: { includes: check.value, position: check.position },
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "toLowerCase") {
        input.data = input.data.toLowerCase();
      } else if (check.kind === "toUpperCase") {
        input.data = input.data.toUpperCase();
      } else if (check.kind === "startsWith") {
        if (!input.data.startsWith(check.value)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: { startsWith: check.value },
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "endsWith") {
        if (!input.data.endsWith(check.value)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: { endsWith: check.value },
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "datetime") {
        const regex = datetimeRegex(check);
        if (!regex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: "datetime",
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "date") {
        const regex = dateRegex;
        if (!regex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: "date",
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "time") {
        const regex = timeRegex(check);
        if (!regex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_string,
            validation: "time",
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "duration") {
        if (!durationRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "duration",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "ip") {
        if (!isValidIP(input.data, check.version)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "ip",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "jwt") {
        if (!isValidJWT(input.data, check.alg)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "jwt",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "cidr") {
        if (!isValidCidr(input.data, check.version)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "cidr",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "base64") {
        if (!base64Regex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "base64",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "base64url") {
        if (!base64urlRegex.test(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            validation: "base64url",
            code: ZodIssueCode.invalid_string,
            message: check.message
          });
          status.dirty();
        }
      } else {
        util.assertNever(check);
      }
    }
    return { status: status.value, value: input.data };
  }
  _regex(regex, validation, message) {
    return this.refinement((data) => regex.test(data), {
      validation,
      code: ZodIssueCode.invalid_string,
      ...errorUtil.errToObj(message)
    });
  }
  _addCheck(check) {
    return new _ZodString({
      ...this._def,
      checks: [...this._def.checks, check]
    });
  }
  email(message) {
    return this._addCheck({ kind: "email", ...errorUtil.errToObj(message) });
  }
  url(message) {
    return this._addCheck({ kind: "url", ...errorUtil.errToObj(message) });
  }
  emoji(message) {
    return this._addCheck({ kind: "emoji", ...errorUtil.errToObj(message) });
  }
  uuid(message) {
    return this._addCheck({ kind: "uuid", ...errorUtil.errToObj(message) });
  }
  nanoid(message) {
    return this._addCheck({ kind: "nanoid", ...errorUtil.errToObj(message) });
  }
  cuid(message) {
    return this._addCheck({ kind: "cuid", ...errorUtil.errToObj(message) });
  }
  cuid2(message) {
    return this._addCheck({ kind: "cuid2", ...errorUtil.errToObj(message) });
  }
  ulid(message) {
    return this._addCheck({ kind: "ulid", ...errorUtil.errToObj(message) });
  }
  base64(message) {
    return this._addCheck({ kind: "base64", ...errorUtil.errToObj(message) });
  }
  base64url(message) {
    return this._addCheck({
      kind: "base64url",
      ...errorUtil.errToObj(message)
    });
  }
  jwt(options) {
    return this._addCheck({ kind: "jwt", ...errorUtil.errToObj(options) });
  }
  ip(options) {
    return this._addCheck({ kind: "ip", ...errorUtil.errToObj(options) });
  }
  cidr(options) {
    return this._addCheck({ kind: "cidr", ...errorUtil.errToObj(options) });
  }
  datetime(options) {
    if (typeof options === "string") {
      return this._addCheck({
        kind: "datetime",
        precision: null,
        offset: false,
        local: false,
        message: options
      });
    }
    return this._addCheck({
      kind: "datetime",
      precision: typeof options?.precision === "undefined" ? null : options?.precision,
      offset: options?.offset ?? false,
      local: options?.local ?? false,
      ...errorUtil.errToObj(options?.message)
    });
  }
  date(message) {
    return this._addCheck({ kind: "date", message });
  }
  time(options) {
    if (typeof options === "string") {
      return this._addCheck({
        kind: "time",
        precision: null,
        message: options
      });
    }
    return this._addCheck({
      kind: "time",
      precision: typeof options?.precision === "undefined" ? null : options?.precision,
      ...errorUtil.errToObj(options?.message)
    });
  }
  duration(message) {
    return this._addCheck({ kind: "duration", ...errorUtil.errToObj(message) });
  }
  regex(regex, message) {
    return this._addCheck({
      kind: "regex",
      regex,
      ...errorUtil.errToObj(message)
    });
  }
  includes(value, options) {
    return this._addCheck({
      kind: "includes",
      value,
      position: options?.position,
      ...errorUtil.errToObj(options?.message)
    });
  }
  startsWith(value, message) {
    return this._addCheck({
      kind: "startsWith",
      value,
      ...errorUtil.errToObj(message)
    });
  }
  endsWith(value, message) {
    return this._addCheck({
      kind: "endsWith",
      value,
      ...errorUtil.errToObj(message)
    });
  }
  min(minLength, message) {
    return this._addCheck({
      kind: "min",
      value: minLength,
      ...errorUtil.errToObj(message)
    });
  }
  max(maxLength, message) {
    return this._addCheck({
      kind: "max",
      value: maxLength,
      ...errorUtil.errToObj(message)
    });
  }
  length(len, message) {
    return this._addCheck({
      kind: "length",
      value: len,
      ...errorUtil.errToObj(message)
    });
  }
  /**
   * Equivalent to `.min(1)`
   */
  nonempty(message) {
    return this.min(1, errorUtil.errToObj(message));
  }
  trim() {
    return new _ZodString({
      ...this._def,
      checks: [...this._def.checks, { kind: "trim" }]
    });
  }
  toLowerCase() {
    return new _ZodString({
      ...this._def,
      checks: [...this._def.checks, { kind: "toLowerCase" }]
    });
  }
  toUpperCase() {
    return new _ZodString({
      ...this._def,
      checks: [...this._def.checks, { kind: "toUpperCase" }]
    });
  }
  get isDatetime() {
    return !!this._def.checks.find((ch) => ch.kind === "datetime");
  }
  get isDate() {
    return !!this._def.checks.find((ch) => ch.kind === "date");
  }
  get isTime() {
    return !!this._def.checks.find((ch) => ch.kind === "time");
  }
  get isDuration() {
    return !!this._def.checks.find((ch) => ch.kind === "duration");
  }
  get isEmail() {
    return !!this._def.checks.find((ch) => ch.kind === "email");
  }
  get isURL() {
    return !!this._def.checks.find((ch) => ch.kind === "url");
  }
  get isEmoji() {
    return !!this._def.checks.find((ch) => ch.kind === "emoji");
  }
  get isUUID() {
    return !!this._def.checks.find((ch) => ch.kind === "uuid");
  }
  get isNANOID() {
    return !!this._def.checks.find((ch) => ch.kind === "nanoid");
  }
  get isCUID() {
    return !!this._def.checks.find((ch) => ch.kind === "cuid");
  }
  get isCUID2() {
    return !!this._def.checks.find((ch) => ch.kind === "cuid2");
  }
  get isULID() {
    return !!this._def.checks.find((ch) => ch.kind === "ulid");
  }
  get isIP() {
    return !!this._def.checks.find((ch) => ch.kind === "ip");
  }
  get isCIDR() {
    return !!this._def.checks.find((ch) => ch.kind === "cidr");
  }
  get isBase64() {
    return !!this._def.checks.find((ch) => ch.kind === "base64");
  }
  get isBase64url() {
    return !!this._def.checks.find((ch) => ch.kind === "base64url");
  }
  get minLength() {
    let min = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "min") {
        if (min === null || ch.value > min)
          min = ch.value;
      }
    }
    return min;
  }
  get maxLength() {
    let max = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "max") {
        if (max === null || ch.value < max)
          max = ch.value;
      }
    }
    return max;
  }
};
ZodString.create = (params) => {
  return new ZodString({
    checks: [],
    typeName: ZodFirstPartyTypeKind.ZodString,
    coerce: params?.coerce ?? false,
    ...processCreateParams(params)
  });
};
function floatSafeRemainder(val, step) {
  const valDecCount = (val.toString().split(".")[1] || "").length;
  const stepDecCount = (step.toString().split(".")[1] || "").length;
  const decCount = valDecCount > stepDecCount ? valDecCount : stepDecCount;
  const valInt = Number.parseInt(val.toFixed(decCount).replace(".", ""));
  const stepInt = Number.parseInt(step.toFixed(decCount).replace(".", ""));
  return valInt % stepInt / 10 ** decCount;
}
var ZodNumber = class _ZodNumber extends ZodType {
  constructor() {
    super(...arguments);
    this.min = this.gte;
    this.max = this.lte;
    this.step = this.multipleOf;
  }
  _parse(input) {
    if (this._def.coerce) {
      input.data = Number(input.data);
    }
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.number) {
      const ctx2 = this._getOrReturnCtx(input);
      addIssueToContext(ctx2, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.number,
        received: ctx2.parsedType
      });
      return INVALID;
    }
    let ctx = void 0;
    const status = new ParseStatus();
    for (const check of this._def.checks) {
      if (check.kind === "int") {
        if (!util.isInteger(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.invalid_type,
            expected: "integer",
            received: "float",
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "min") {
        const tooSmall = check.inclusive ? input.data < check.value : input.data <= check.value;
        if (tooSmall) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_small,
            minimum: check.value,
            type: "number",
            inclusive: check.inclusive,
            exact: false,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "max") {
        const tooBig = check.inclusive ? input.data > check.value : input.data >= check.value;
        if (tooBig) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_big,
            maximum: check.value,
            type: "number",
            inclusive: check.inclusive,
            exact: false,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "multipleOf") {
        if (floatSafeRemainder(input.data, check.value) !== 0) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.not_multiple_of,
            multipleOf: check.value,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "finite") {
        if (!Number.isFinite(input.data)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.not_finite,
            message: check.message
          });
          status.dirty();
        }
      } else {
        util.assertNever(check);
      }
    }
    return { status: status.value, value: input.data };
  }
  gte(value, message) {
    return this.setLimit("min", value, true, errorUtil.toString(message));
  }
  gt(value, message) {
    return this.setLimit("min", value, false, errorUtil.toString(message));
  }
  lte(value, message) {
    return this.setLimit("max", value, true, errorUtil.toString(message));
  }
  lt(value, message) {
    return this.setLimit("max", value, false, errorUtil.toString(message));
  }
  setLimit(kind, value, inclusive, message) {
    return new _ZodNumber({
      ...this._def,
      checks: [
        ...this._def.checks,
        {
          kind,
          value,
          inclusive,
          message: errorUtil.toString(message)
        }
      ]
    });
  }
  _addCheck(check) {
    return new _ZodNumber({
      ...this._def,
      checks: [...this._def.checks, check]
    });
  }
  int(message) {
    return this._addCheck({
      kind: "int",
      message: errorUtil.toString(message)
    });
  }
  positive(message) {
    return this._addCheck({
      kind: "min",
      value: 0,
      inclusive: false,
      message: errorUtil.toString(message)
    });
  }
  negative(message) {
    return this._addCheck({
      kind: "max",
      value: 0,
      inclusive: false,
      message: errorUtil.toString(message)
    });
  }
  nonpositive(message) {
    return this._addCheck({
      kind: "max",
      value: 0,
      inclusive: true,
      message: errorUtil.toString(message)
    });
  }
  nonnegative(message) {
    return this._addCheck({
      kind: "min",
      value: 0,
      inclusive: true,
      message: errorUtil.toString(message)
    });
  }
  multipleOf(value, message) {
    return this._addCheck({
      kind: "multipleOf",
      value,
      message: errorUtil.toString(message)
    });
  }
  finite(message) {
    return this._addCheck({
      kind: "finite",
      message: errorUtil.toString(message)
    });
  }
  safe(message) {
    return this._addCheck({
      kind: "min",
      inclusive: true,
      value: Number.MIN_SAFE_INTEGER,
      message: errorUtil.toString(message)
    })._addCheck({
      kind: "max",
      inclusive: true,
      value: Number.MAX_SAFE_INTEGER,
      message: errorUtil.toString(message)
    });
  }
  get minValue() {
    let min = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "min") {
        if (min === null || ch.value > min)
          min = ch.value;
      }
    }
    return min;
  }
  get maxValue() {
    let max = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "max") {
        if (max === null || ch.value < max)
          max = ch.value;
      }
    }
    return max;
  }
  get isInt() {
    return !!this._def.checks.find((ch) => ch.kind === "int" || ch.kind === "multipleOf" && util.isInteger(ch.value));
  }
  get isFinite() {
    let max = null;
    let min = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "finite" || ch.kind === "int" || ch.kind === "multipleOf") {
        return true;
      } else if (ch.kind === "min") {
        if (min === null || ch.value > min)
          min = ch.value;
      } else if (ch.kind === "max") {
        if (max === null || ch.value < max)
          max = ch.value;
      }
    }
    return Number.isFinite(min) && Number.isFinite(max);
  }
};
ZodNumber.create = (params) => {
  return new ZodNumber({
    checks: [],
    typeName: ZodFirstPartyTypeKind.ZodNumber,
    coerce: params?.coerce || false,
    ...processCreateParams(params)
  });
};
var ZodBigInt = class _ZodBigInt extends ZodType {
  constructor() {
    super(...arguments);
    this.min = this.gte;
    this.max = this.lte;
  }
  _parse(input) {
    if (this._def.coerce) {
      try {
        input.data = BigInt(input.data);
      } catch {
        return this._getInvalidInput(input);
      }
    }
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.bigint) {
      return this._getInvalidInput(input);
    }
    let ctx = void 0;
    const status = new ParseStatus();
    for (const check of this._def.checks) {
      if (check.kind === "min") {
        const tooSmall = check.inclusive ? input.data < check.value : input.data <= check.value;
        if (tooSmall) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_small,
            type: "bigint",
            minimum: check.value,
            inclusive: check.inclusive,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "max") {
        const tooBig = check.inclusive ? input.data > check.value : input.data >= check.value;
        if (tooBig) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_big,
            type: "bigint",
            maximum: check.value,
            inclusive: check.inclusive,
            message: check.message
          });
          status.dirty();
        }
      } else if (check.kind === "multipleOf") {
        if (input.data % check.value !== BigInt(0)) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.not_multiple_of,
            multipleOf: check.value,
            message: check.message
          });
          status.dirty();
        }
      } else {
        util.assertNever(check);
      }
    }
    return { status: status.value, value: input.data };
  }
  _getInvalidInput(input) {
    const ctx = this._getOrReturnCtx(input);
    addIssueToContext(ctx, {
      code: ZodIssueCode.invalid_type,
      expected: ZodParsedType.bigint,
      received: ctx.parsedType
    });
    return INVALID;
  }
  gte(value, message) {
    return this.setLimit("min", value, true, errorUtil.toString(message));
  }
  gt(value, message) {
    return this.setLimit("min", value, false, errorUtil.toString(message));
  }
  lte(value, message) {
    return this.setLimit("max", value, true, errorUtil.toString(message));
  }
  lt(value, message) {
    return this.setLimit("max", value, false, errorUtil.toString(message));
  }
  setLimit(kind, value, inclusive, message) {
    return new _ZodBigInt({
      ...this._def,
      checks: [
        ...this._def.checks,
        {
          kind,
          value,
          inclusive,
          message: errorUtil.toString(message)
        }
      ]
    });
  }
  _addCheck(check) {
    return new _ZodBigInt({
      ...this._def,
      checks: [...this._def.checks, check]
    });
  }
  positive(message) {
    return this._addCheck({
      kind: "min",
      value: BigInt(0),
      inclusive: false,
      message: errorUtil.toString(message)
    });
  }
  negative(message) {
    return this._addCheck({
      kind: "max",
      value: BigInt(0),
      inclusive: false,
      message: errorUtil.toString(message)
    });
  }
  nonpositive(message) {
    return this._addCheck({
      kind: "max",
      value: BigInt(0),
      inclusive: true,
      message: errorUtil.toString(message)
    });
  }
  nonnegative(message) {
    return this._addCheck({
      kind: "min",
      value: BigInt(0),
      inclusive: true,
      message: errorUtil.toString(message)
    });
  }
  multipleOf(value, message) {
    return this._addCheck({
      kind: "multipleOf",
      value,
      message: errorUtil.toString(message)
    });
  }
  get minValue() {
    let min = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "min") {
        if (min === null || ch.value > min)
          min = ch.value;
      }
    }
    return min;
  }
  get maxValue() {
    let max = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "max") {
        if (max === null || ch.value < max)
          max = ch.value;
      }
    }
    return max;
  }
};
ZodBigInt.create = (params) => {
  return new ZodBigInt({
    checks: [],
    typeName: ZodFirstPartyTypeKind.ZodBigInt,
    coerce: params?.coerce ?? false,
    ...processCreateParams(params)
  });
};
var ZodBoolean = class extends ZodType {
  _parse(input) {
    if (this._def.coerce) {
      input.data = Boolean(input.data);
    }
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.boolean) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.boolean,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return OK(input.data);
  }
};
ZodBoolean.create = (params) => {
  return new ZodBoolean({
    typeName: ZodFirstPartyTypeKind.ZodBoolean,
    coerce: params?.coerce || false,
    ...processCreateParams(params)
  });
};
var ZodDate = class _ZodDate extends ZodType {
  _parse(input) {
    if (this._def.coerce) {
      input.data = new Date(input.data);
    }
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.date) {
      const ctx2 = this._getOrReturnCtx(input);
      addIssueToContext(ctx2, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.date,
        received: ctx2.parsedType
      });
      return INVALID;
    }
    if (Number.isNaN(input.data.getTime())) {
      const ctx2 = this._getOrReturnCtx(input);
      addIssueToContext(ctx2, {
        code: ZodIssueCode.invalid_date
      });
      return INVALID;
    }
    const status = new ParseStatus();
    let ctx = void 0;
    for (const check of this._def.checks) {
      if (check.kind === "min") {
        if (input.data.getTime() < check.value) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_small,
            message: check.message,
            inclusive: true,
            exact: false,
            minimum: check.value,
            type: "date"
          });
          status.dirty();
        }
      } else if (check.kind === "max") {
        if (input.data.getTime() > check.value) {
          ctx = this._getOrReturnCtx(input, ctx);
          addIssueToContext(ctx, {
            code: ZodIssueCode.too_big,
            message: check.message,
            inclusive: true,
            exact: false,
            maximum: check.value,
            type: "date"
          });
          status.dirty();
        }
      } else {
        util.assertNever(check);
      }
    }
    return {
      status: status.value,
      value: new Date(input.data.getTime())
    };
  }
  _addCheck(check) {
    return new _ZodDate({
      ...this._def,
      checks: [...this._def.checks, check]
    });
  }
  min(minDate, message) {
    return this._addCheck({
      kind: "min",
      value: minDate.getTime(),
      message: errorUtil.toString(message)
    });
  }
  max(maxDate, message) {
    return this._addCheck({
      kind: "max",
      value: maxDate.getTime(),
      message: errorUtil.toString(message)
    });
  }
  get minDate() {
    let min = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "min") {
        if (min === null || ch.value > min)
          min = ch.value;
      }
    }
    return min != null ? new Date(min) : null;
  }
  get maxDate() {
    let max = null;
    for (const ch of this._def.checks) {
      if (ch.kind === "max") {
        if (max === null || ch.value < max)
          max = ch.value;
      }
    }
    return max != null ? new Date(max) : null;
  }
};
ZodDate.create = (params) => {
  return new ZodDate({
    checks: [],
    coerce: params?.coerce || false,
    typeName: ZodFirstPartyTypeKind.ZodDate,
    ...processCreateParams(params)
  });
};
var ZodSymbol = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.symbol) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.symbol,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return OK(input.data);
  }
};
ZodSymbol.create = (params) => {
  return new ZodSymbol({
    typeName: ZodFirstPartyTypeKind.ZodSymbol,
    ...processCreateParams(params)
  });
};
var ZodUndefined = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.undefined) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.undefined,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return OK(input.data);
  }
};
ZodUndefined.create = (params) => {
  return new ZodUndefined({
    typeName: ZodFirstPartyTypeKind.ZodUndefined,
    ...processCreateParams(params)
  });
};
var ZodNull = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.null) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.null,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return OK(input.data);
  }
};
ZodNull.create = (params) => {
  return new ZodNull({
    typeName: ZodFirstPartyTypeKind.ZodNull,
    ...processCreateParams(params)
  });
};
var ZodAny = class extends ZodType {
  constructor() {
    super(...arguments);
    this._any = true;
  }
  _parse(input) {
    return OK(input.data);
  }
};
ZodAny.create = (params) => {
  return new ZodAny({
    typeName: ZodFirstPartyTypeKind.ZodAny,
    ...processCreateParams(params)
  });
};
var ZodUnknown = class extends ZodType {
  constructor() {
    super(...arguments);
    this._unknown = true;
  }
  _parse(input) {
    return OK(input.data);
  }
};
ZodUnknown.create = (params) => {
  return new ZodUnknown({
    typeName: ZodFirstPartyTypeKind.ZodUnknown,
    ...processCreateParams(params)
  });
};
var ZodNever = class extends ZodType {
  _parse(input) {
    const ctx = this._getOrReturnCtx(input);
    addIssueToContext(ctx, {
      code: ZodIssueCode.invalid_type,
      expected: ZodParsedType.never,
      received: ctx.parsedType
    });
    return INVALID;
  }
};
ZodNever.create = (params) => {
  return new ZodNever({
    typeName: ZodFirstPartyTypeKind.ZodNever,
    ...processCreateParams(params)
  });
};
var ZodVoid = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.undefined) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.void,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return OK(input.data);
  }
};
ZodVoid.create = (params) => {
  return new ZodVoid({
    typeName: ZodFirstPartyTypeKind.ZodVoid,
    ...processCreateParams(params)
  });
};
var ZodArray = class _ZodArray extends ZodType {
  _parse(input) {
    const { ctx, status } = this._processInputParams(input);
    const def = this._def;
    if (ctx.parsedType !== ZodParsedType.array) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.array,
        received: ctx.parsedType
      });
      return INVALID;
    }
    if (def.exactLength !== null) {
      const tooBig = ctx.data.length > def.exactLength.value;
      const tooSmall = ctx.data.length < def.exactLength.value;
      if (tooBig || tooSmall) {
        addIssueToContext(ctx, {
          code: tooBig ? ZodIssueCode.too_big : ZodIssueCode.too_small,
          minimum: tooSmall ? def.exactLength.value : void 0,
          maximum: tooBig ? def.exactLength.value : void 0,
          type: "array",
          inclusive: true,
          exact: true,
          message: def.exactLength.message
        });
        status.dirty();
      }
    }
    if (def.minLength !== null) {
      if (ctx.data.length < def.minLength.value) {
        addIssueToContext(ctx, {
          code: ZodIssueCode.too_small,
          minimum: def.minLength.value,
          type: "array",
          inclusive: true,
          exact: false,
          message: def.minLength.message
        });
        status.dirty();
      }
    }
    if (def.maxLength !== null) {
      if (ctx.data.length > def.maxLength.value) {
        addIssueToContext(ctx, {
          code: ZodIssueCode.too_big,
          maximum: def.maxLength.value,
          type: "array",
          inclusive: true,
          exact: false,
          message: def.maxLength.message
        });
        status.dirty();
      }
    }
    if (ctx.common.async) {
      return Promise.all([...ctx.data].map((item, i) => {
        return def.type._parseAsync(new ParseInputLazyPath(ctx, item, ctx.path, i));
      })).then((result3) => {
        return ParseStatus.mergeArray(status, result3);
      });
    }
    const result2 = [...ctx.data].map((item, i) => {
      return def.type._parseSync(new ParseInputLazyPath(ctx, item, ctx.path, i));
    });
    return ParseStatus.mergeArray(status, result2);
  }
  get element() {
    return this._def.type;
  }
  min(minLength, message) {
    return new _ZodArray({
      ...this._def,
      minLength: { value: minLength, message: errorUtil.toString(message) }
    });
  }
  max(maxLength, message) {
    return new _ZodArray({
      ...this._def,
      maxLength: { value: maxLength, message: errorUtil.toString(message) }
    });
  }
  length(len, message) {
    return new _ZodArray({
      ...this._def,
      exactLength: { value: len, message: errorUtil.toString(message) }
    });
  }
  nonempty(message) {
    return this.min(1, message);
  }
};
ZodArray.create = (schema2, params) => {
  return new ZodArray({
    type: schema2,
    minLength: null,
    maxLength: null,
    exactLength: null,
    typeName: ZodFirstPartyTypeKind.ZodArray,
    ...processCreateParams(params)
  });
};
function deepPartialify(schema2) {
  if (schema2 instanceof ZodObject) {
    const newShape = {};
    for (const key in schema2.shape) {
      const fieldSchema = schema2.shape[key];
      newShape[key] = ZodOptional.create(deepPartialify(fieldSchema));
    }
    return new ZodObject({
      ...schema2._def,
      shape: () => newShape
    });
  } else if (schema2 instanceof ZodArray) {
    return new ZodArray({
      ...schema2._def,
      type: deepPartialify(schema2.element)
    });
  } else if (schema2 instanceof ZodOptional) {
    return ZodOptional.create(deepPartialify(schema2.unwrap()));
  } else if (schema2 instanceof ZodNullable) {
    return ZodNullable.create(deepPartialify(schema2.unwrap()));
  } else if (schema2 instanceof ZodTuple) {
    return ZodTuple.create(schema2.items.map((item) => deepPartialify(item)));
  } else {
    return schema2;
  }
}
var ZodObject = class _ZodObject extends ZodType {
  constructor() {
    super(...arguments);
    this._cached = null;
    this.nonstrict = this.passthrough;
    this.augment = this.extend;
  }
  _getCached() {
    if (this._cached !== null)
      return this._cached;
    const shape = this._def.shape();
    const keys = util.objectKeys(shape);
    this._cached = { shape, keys };
    return this._cached;
  }
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.object) {
      const ctx2 = this._getOrReturnCtx(input);
      addIssueToContext(ctx2, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.object,
        received: ctx2.parsedType
      });
      return INVALID;
    }
    const { status, ctx } = this._processInputParams(input);
    const { shape, keys: shapeKeys } = this._getCached();
    const extraKeys = [];
    if (!(this._def.catchall instanceof ZodNever && this._def.unknownKeys === "strip")) {
      for (const key in ctx.data) {
        if (!shapeKeys.includes(key)) {
          extraKeys.push(key);
        }
      }
    }
    const pairs = [];
    for (const key of shapeKeys) {
      const keyValidator = shape[key];
      const value = ctx.data[key];
      pairs.push({
        key: { status: "valid", value: key },
        value: keyValidator._parse(new ParseInputLazyPath(ctx, value, ctx.path, key)),
        alwaysSet: key in ctx.data
      });
    }
    if (this._def.catchall instanceof ZodNever) {
      const unknownKeys = this._def.unknownKeys;
      if (unknownKeys === "passthrough") {
        for (const key of extraKeys) {
          pairs.push({
            key: { status: "valid", value: key },
            value: { status: "valid", value: ctx.data[key] }
          });
        }
      } else if (unknownKeys === "strict") {
        if (extraKeys.length > 0) {
          addIssueToContext(ctx, {
            code: ZodIssueCode.unrecognized_keys,
            keys: extraKeys
          });
          status.dirty();
        }
      } else if (unknownKeys === "strip") {
      } else {
        throw new Error(`Internal ZodObject error: invalid unknownKeys value.`);
      }
    } else {
      const catchall = this._def.catchall;
      for (const key of extraKeys) {
        const value = ctx.data[key];
        pairs.push({
          key: { status: "valid", value: key },
          value: catchall._parse(
            new ParseInputLazyPath(ctx, value, ctx.path, key)
            //, ctx.child(key), value, getParsedType(value)
          ),
          alwaysSet: key in ctx.data
        });
      }
    }
    if (ctx.common.async) {
      return Promise.resolve().then(async () => {
        const syncPairs = [];
        for (const pair of pairs) {
          const key = await pair.key;
          const value = await pair.value;
          syncPairs.push({
            key,
            value,
            alwaysSet: pair.alwaysSet
          });
        }
        return syncPairs;
      }).then((syncPairs) => {
        return ParseStatus.mergeObjectSync(status, syncPairs);
      });
    } else {
      return ParseStatus.mergeObjectSync(status, pairs);
    }
  }
  get shape() {
    return this._def.shape();
  }
  strict(message) {
    errorUtil.errToObj;
    return new _ZodObject({
      ...this._def,
      unknownKeys: "strict",
      ...message !== void 0 ? {
        errorMap: (issue, ctx) => {
          const defaultError = this._def.errorMap?.(issue, ctx).message ?? ctx.defaultError;
          if (issue.code === "unrecognized_keys")
            return {
              message: errorUtil.errToObj(message).message ?? defaultError
            };
          return {
            message: defaultError
          };
        }
      } : {}
    });
  }
  strip() {
    return new _ZodObject({
      ...this._def,
      unknownKeys: "strip"
    });
  }
  passthrough() {
    return new _ZodObject({
      ...this._def,
      unknownKeys: "passthrough"
    });
  }
  // const AugmentFactory =
  //   <Def extends ZodObjectDef>(def: Def) =>
  //   <Augmentation extends ZodRawShape>(
  //     augmentation: Augmentation
  //   ): ZodObject<
  //     extendShape<ReturnType<Def["shape"]>, Augmentation>,
  //     Def["unknownKeys"],
  //     Def["catchall"]
  //   > => {
  //     return new ZodObject({
  //       ...def,
  //       shape: () => ({
  //         ...def.shape(),
  //         ...augmentation,
  //       }),
  //     }) as any;
  //   };
  extend(augmentation) {
    return new _ZodObject({
      ...this._def,
      shape: () => ({
        ...this._def.shape(),
        ...augmentation
      })
    });
  }
  /**
   * Prior to zod@1.0.12 there was a bug in the
   * inferred type of merged objects. Please
   * upgrade if you are experiencing issues.
   */
  merge(merging) {
    const merged = new _ZodObject({
      unknownKeys: merging._def.unknownKeys,
      catchall: merging._def.catchall,
      shape: () => ({
        ...this._def.shape(),
        ...merging._def.shape()
      }),
      typeName: ZodFirstPartyTypeKind.ZodObject
    });
    return merged;
  }
  // merge<
  //   Incoming extends AnyZodObject,
  //   Augmentation extends Incoming["shape"],
  //   NewOutput extends {
  //     [k in keyof Augmentation | keyof Output]: k extends keyof Augmentation
  //       ? Augmentation[k]["_output"]
  //       : k extends keyof Output
  //       ? Output[k]
  //       : never;
  //   },
  //   NewInput extends {
  //     [k in keyof Augmentation | keyof Input]: k extends keyof Augmentation
  //       ? Augmentation[k]["_input"]
  //       : k extends keyof Input
  //       ? Input[k]
  //       : never;
  //   }
  // >(
  //   merging: Incoming
  // ): ZodObject<
  //   extendShape<T, ReturnType<Incoming["_def"]["shape"]>>,
  //   Incoming["_def"]["unknownKeys"],
  //   Incoming["_def"]["catchall"],
  //   NewOutput,
  //   NewInput
  // > {
  //   const merged: any = new ZodObject({
  //     unknownKeys: merging._def.unknownKeys,
  //     catchall: merging._def.catchall,
  //     shape: () =>
  //       objectUtil.mergeShapes(this._def.shape(), merging._def.shape()),
  //     typeName: ZodFirstPartyTypeKind.ZodObject,
  //   }) as any;
  //   return merged;
  // }
  setKey(key, schema2) {
    return this.augment({ [key]: schema2 });
  }
  // merge<Incoming extends AnyZodObject>(
  //   merging: Incoming
  // ): //ZodObject<T & Incoming["_shape"], UnknownKeys, Catchall> = (merging) => {
  // ZodObject<
  //   extendShape<T, ReturnType<Incoming["_def"]["shape"]>>,
  //   Incoming["_def"]["unknownKeys"],
  //   Incoming["_def"]["catchall"]
  // > {
  //   // const mergedShape = objectUtil.mergeShapes(
  //   //   this._def.shape(),
  //   //   merging._def.shape()
  //   // );
  //   const merged: any = new ZodObject({
  //     unknownKeys: merging._def.unknownKeys,
  //     catchall: merging._def.catchall,
  //     shape: () =>
  //       objectUtil.mergeShapes(this._def.shape(), merging._def.shape()),
  //     typeName: ZodFirstPartyTypeKind.ZodObject,
  //   }) as any;
  //   return merged;
  // }
  catchall(index) {
    return new _ZodObject({
      ...this._def,
      catchall: index
    });
  }
  pick(mask) {
    const shape = {};
    for (const key of util.objectKeys(mask)) {
      if (mask[key] && this.shape[key]) {
        shape[key] = this.shape[key];
      }
    }
    return new _ZodObject({
      ...this._def,
      shape: () => shape
    });
  }
  omit(mask) {
    const shape = {};
    for (const key of util.objectKeys(this.shape)) {
      if (!mask[key]) {
        shape[key] = this.shape[key];
      }
    }
    return new _ZodObject({
      ...this._def,
      shape: () => shape
    });
  }
  /**
   * @deprecated
   */
  deepPartial() {
    return deepPartialify(this);
  }
  partial(mask) {
    const newShape = {};
    for (const key of util.objectKeys(this.shape)) {
      const fieldSchema = this.shape[key];
      if (mask && !mask[key]) {
        newShape[key] = fieldSchema;
      } else {
        newShape[key] = fieldSchema.optional();
      }
    }
    return new _ZodObject({
      ...this._def,
      shape: () => newShape
    });
  }
  required(mask) {
    const newShape = {};
    for (const key of util.objectKeys(this.shape)) {
      if (mask && !mask[key]) {
        newShape[key] = this.shape[key];
      } else {
        const fieldSchema = this.shape[key];
        let newField = fieldSchema;
        while (newField instanceof ZodOptional) {
          newField = newField._def.innerType;
        }
        newShape[key] = newField;
      }
    }
    return new _ZodObject({
      ...this._def,
      shape: () => newShape
    });
  }
  keyof() {
    return createZodEnum(util.objectKeys(this.shape));
  }
};
ZodObject.create = (shape, params) => {
  return new ZodObject({
    shape: () => shape,
    unknownKeys: "strip",
    catchall: ZodNever.create(),
    typeName: ZodFirstPartyTypeKind.ZodObject,
    ...processCreateParams(params)
  });
};
ZodObject.strictCreate = (shape, params) => {
  return new ZodObject({
    shape: () => shape,
    unknownKeys: "strict",
    catchall: ZodNever.create(),
    typeName: ZodFirstPartyTypeKind.ZodObject,
    ...processCreateParams(params)
  });
};
ZodObject.lazycreate = (shape, params) => {
  return new ZodObject({
    shape,
    unknownKeys: "strip",
    catchall: ZodNever.create(),
    typeName: ZodFirstPartyTypeKind.ZodObject,
    ...processCreateParams(params)
  });
};
var ZodUnion = class extends ZodType {
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    const options = this._def.options;
    function handleResults(results) {
      for (const result2 of results) {
        if (result2.result.status === "valid") {
          return result2.result;
        }
      }
      for (const result2 of results) {
        if (result2.result.status === "dirty") {
          ctx.common.issues.push(...result2.ctx.common.issues);
          return result2.result;
        }
      }
      const unionErrors = results.map((result2) => new ZodError(result2.ctx.common.issues));
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_union,
        unionErrors
      });
      return INVALID;
    }
    if (ctx.common.async) {
      return Promise.all(options.map(async (option) => {
        const childCtx = {
          ...ctx,
          common: {
            ...ctx.common,
            issues: []
          },
          parent: null
        };
        return {
          result: await option._parseAsync({
            data: ctx.data,
            path: ctx.path,
            parent: childCtx
          }),
          ctx: childCtx
        };
      })).then(handleResults);
    } else {
      let dirty = void 0;
      const issues = [];
      for (const option of options) {
        const childCtx = {
          ...ctx,
          common: {
            ...ctx.common,
            issues: []
          },
          parent: null
        };
        const result2 = option._parseSync({
          data: ctx.data,
          path: ctx.path,
          parent: childCtx
        });
        if (result2.status === "valid") {
          return result2;
        } else if (result2.status === "dirty" && !dirty) {
          dirty = { result: result2, ctx: childCtx };
        }
        if (childCtx.common.issues.length) {
          issues.push(childCtx.common.issues);
        }
      }
      if (dirty) {
        ctx.common.issues.push(...dirty.ctx.common.issues);
        return dirty.result;
      }
      const unionErrors = issues.map((issues2) => new ZodError(issues2));
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_union,
        unionErrors
      });
      return INVALID;
    }
  }
  get options() {
    return this._def.options;
  }
};
ZodUnion.create = (types, params) => {
  return new ZodUnion({
    options: types,
    typeName: ZodFirstPartyTypeKind.ZodUnion,
    ...processCreateParams(params)
  });
};
var getDiscriminator = (type) => {
  if (type instanceof ZodLazy) {
    return getDiscriminator(type.schema);
  } else if (type instanceof ZodEffects) {
    return getDiscriminator(type.innerType());
  } else if (type instanceof ZodLiteral) {
    return [type.value];
  } else if (type instanceof ZodEnum) {
    return type.options;
  } else if (type instanceof ZodNativeEnum) {
    return util.objectValues(type.enum);
  } else if (type instanceof ZodDefault) {
    return getDiscriminator(type._def.innerType);
  } else if (type instanceof ZodUndefined) {
    return [void 0];
  } else if (type instanceof ZodNull) {
    return [null];
  } else if (type instanceof ZodOptional) {
    return [void 0, ...getDiscriminator(type.unwrap())];
  } else if (type instanceof ZodNullable) {
    return [null, ...getDiscriminator(type.unwrap())];
  } else if (type instanceof ZodBranded) {
    return getDiscriminator(type.unwrap());
  } else if (type instanceof ZodReadonly) {
    return getDiscriminator(type.unwrap());
  } else if (type instanceof ZodCatch) {
    return getDiscriminator(type._def.innerType);
  } else {
    return [];
  }
};
var ZodDiscriminatedUnion = class _ZodDiscriminatedUnion extends ZodType {
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.object) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.object,
        received: ctx.parsedType
      });
      return INVALID;
    }
    const discriminator = this.discriminator;
    const discriminatorValue = ctx.data[discriminator];
    const option = this.optionsMap.get(discriminatorValue);
    if (!option) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_union_discriminator,
        options: Array.from(this.optionsMap.keys()),
        path: [discriminator]
      });
      return INVALID;
    }
    if (ctx.common.async) {
      return option._parseAsync({
        data: ctx.data,
        path: ctx.path,
        parent: ctx
      });
    } else {
      return option._parseSync({
        data: ctx.data,
        path: ctx.path,
        parent: ctx
      });
    }
  }
  get discriminator() {
    return this._def.discriminator;
  }
  get options() {
    return this._def.options;
  }
  get optionsMap() {
    return this._def.optionsMap;
  }
  /**
   * The constructor of the discriminated union schema. Its behaviour is very similar to that of the normal z.union() constructor.
   * However, it only allows a union of objects, all of which need to share a discriminator property. This property must
   * have a different value for each object in the union.
   * @param discriminator the name of the discriminator property
   * @param types an array of object schemas
   * @param params
   */
  static create(discriminator, options, params) {
    const optionsMap = /* @__PURE__ */ new Map();
    for (const type of options) {
      const discriminatorValues = getDiscriminator(type.shape[discriminator]);
      if (!discriminatorValues.length) {
        throw new Error(`A discriminator value for key \`${discriminator}\` could not be extracted from all schema options`);
      }
      for (const value of discriminatorValues) {
        if (optionsMap.has(value)) {
          throw new Error(`Discriminator property ${String(discriminator)} has duplicate value ${String(value)}`);
        }
        optionsMap.set(value, type);
      }
    }
    return new _ZodDiscriminatedUnion({
      typeName: ZodFirstPartyTypeKind.ZodDiscriminatedUnion,
      discriminator,
      options,
      optionsMap,
      ...processCreateParams(params)
    });
  }
};
function mergeValues(a, b) {
  const aType = getParsedType(a);
  const bType = getParsedType(b);
  if (a === b) {
    return { valid: true, data: a };
  } else if (aType === ZodParsedType.object && bType === ZodParsedType.object) {
    const bKeys = util.objectKeys(b);
    const sharedKeys = util.objectKeys(a).filter((key) => bKeys.indexOf(key) !== -1);
    const newObj = { ...a, ...b };
    for (const key of sharedKeys) {
      const sharedValue = mergeValues(a[key], b[key]);
      if (!sharedValue.valid) {
        return { valid: false };
      }
      newObj[key] = sharedValue.data;
    }
    return { valid: true, data: newObj };
  } else if (aType === ZodParsedType.array && bType === ZodParsedType.array) {
    if (a.length !== b.length) {
      return { valid: false };
    }
    const newArray = [];
    for (let index = 0; index < a.length; index++) {
      const itemA = a[index];
      const itemB = b[index];
      const sharedValue = mergeValues(itemA, itemB);
      if (!sharedValue.valid) {
        return { valid: false };
      }
      newArray.push(sharedValue.data);
    }
    return { valid: true, data: newArray };
  } else if (aType === ZodParsedType.date && bType === ZodParsedType.date && +a === +b) {
    return { valid: true, data: a };
  } else {
    return { valid: false };
  }
}
var ZodIntersection = class extends ZodType {
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    const handleParsed = (parsedLeft, parsedRight) => {
      if (isAborted(parsedLeft) || isAborted(parsedRight)) {
        return INVALID;
      }
      const merged = mergeValues(parsedLeft.value, parsedRight.value);
      if (!merged.valid) {
        addIssueToContext(ctx, {
          code: ZodIssueCode.invalid_intersection_types
        });
        return INVALID;
      }
      if (isDirty(parsedLeft) || isDirty(parsedRight)) {
        status.dirty();
      }
      return { status: status.value, value: merged.data };
    };
    if (ctx.common.async) {
      return Promise.all([
        this._def.left._parseAsync({
          data: ctx.data,
          path: ctx.path,
          parent: ctx
        }),
        this._def.right._parseAsync({
          data: ctx.data,
          path: ctx.path,
          parent: ctx
        })
      ]).then(([left, right]) => handleParsed(left, right));
    } else {
      return handleParsed(this._def.left._parseSync({
        data: ctx.data,
        path: ctx.path,
        parent: ctx
      }), this._def.right._parseSync({
        data: ctx.data,
        path: ctx.path,
        parent: ctx
      }));
    }
  }
};
ZodIntersection.create = (left, right, params) => {
  return new ZodIntersection({
    left,
    right,
    typeName: ZodFirstPartyTypeKind.ZodIntersection,
    ...processCreateParams(params)
  });
};
var ZodTuple = class _ZodTuple extends ZodType {
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.array) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.array,
        received: ctx.parsedType
      });
      return INVALID;
    }
    if (ctx.data.length < this._def.items.length) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.too_small,
        minimum: this._def.items.length,
        inclusive: true,
        exact: false,
        type: "array"
      });
      return INVALID;
    }
    const rest = this._def.rest;
    if (!rest && ctx.data.length > this._def.items.length) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.too_big,
        maximum: this._def.items.length,
        inclusive: true,
        exact: false,
        type: "array"
      });
      status.dirty();
    }
    const items = [...ctx.data].map((item, itemIndex) => {
      const schema2 = this._def.items[itemIndex] || this._def.rest;
      if (!schema2)
        return null;
      return schema2._parse(new ParseInputLazyPath(ctx, item, ctx.path, itemIndex));
    }).filter((x) => !!x);
    if (ctx.common.async) {
      return Promise.all(items).then((results) => {
        return ParseStatus.mergeArray(status, results);
      });
    } else {
      return ParseStatus.mergeArray(status, items);
    }
  }
  get items() {
    return this._def.items;
  }
  rest(rest) {
    return new _ZodTuple({
      ...this._def,
      rest
    });
  }
};
ZodTuple.create = (schemas, params) => {
  if (!Array.isArray(schemas)) {
    throw new Error("You must pass an array of schemas to z.tuple([ ... ])");
  }
  return new ZodTuple({
    items: schemas,
    typeName: ZodFirstPartyTypeKind.ZodTuple,
    rest: null,
    ...processCreateParams(params)
  });
};
var ZodRecord = class _ZodRecord extends ZodType {
  get keySchema() {
    return this._def.keyType;
  }
  get valueSchema() {
    return this._def.valueType;
  }
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.object) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.object,
        received: ctx.parsedType
      });
      return INVALID;
    }
    const pairs = [];
    const keyType = this._def.keyType;
    const valueType = this._def.valueType;
    for (const key in ctx.data) {
      pairs.push({
        key: keyType._parse(new ParseInputLazyPath(ctx, key, ctx.path, key)),
        value: valueType._parse(new ParseInputLazyPath(ctx, ctx.data[key], ctx.path, key)),
        alwaysSet: key in ctx.data
      });
    }
    if (ctx.common.async) {
      return ParseStatus.mergeObjectAsync(status, pairs);
    } else {
      return ParseStatus.mergeObjectSync(status, pairs);
    }
  }
  get element() {
    return this._def.valueType;
  }
  static create(first, second, third) {
    if (second instanceof ZodType) {
      return new _ZodRecord({
        keyType: first,
        valueType: second,
        typeName: ZodFirstPartyTypeKind.ZodRecord,
        ...processCreateParams(third)
      });
    }
    return new _ZodRecord({
      keyType: ZodString.create(),
      valueType: first,
      typeName: ZodFirstPartyTypeKind.ZodRecord,
      ...processCreateParams(second)
    });
  }
};
var ZodMap = class extends ZodType {
  get keySchema() {
    return this._def.keyType;
  }
  get valueSchema() {
    return this._def.valueType;
  }
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.map) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.map,
        received: ctx.parsedType
      });
      return INVALID;
    }
    const keyType = this._def.keyType;
    const valueType = this._def.valueType;
    const pairs = [...ctx.data.entries()].map(([key, value], index) => {
      return {
        key: keyType._parse(new ParseInputLazyPath(ctx, key, ctx.path, [index, "key"])),
        value: valueType._parse(new ParseInputLazyPath(ctx, value, ctx.path, [index, "value"]))
      };
    });
    if (ctx.common.async) {
      const finalMap = /* @__PURE__ */ new Map();
      return Promise.resolve().then(async () => {
        for (const pair of pairs) {
          const key = await pair.key;
          const value = await pair.value;
          if (key.status === "aborted" || value.status === "aborted") {
            return INVALID;
          }
          if (key.status === "dirty" || value.status === "dirty") {
            status.dirty();
          }
          finalMap.set(key.value, value.value);
        }
        return { status: status.value, value: finalMap };
      });
    } else {
      const finalMap = /* @__PURE__ */ new Map();
      for (const pair of pairs) {
        const key = pair.key;
        const value = pair.value;
        if (key.status === "aborted" || value.status === "aborted") {
          return INVALID;
        }
        if (key.status === "dirty" || value.status === "dirty") {
          status.dirty();
        }
        finalMap.set(key.value, value.value);
      }
      return { status: status.value, value: finalMap };
    }
  }
};
ZodMap.create = (keyType, valueType, params) => {
  return new ZodMap({
    valueType,
    keyType,
    typeName: ZodFirstPartyTypeKind.ZodMap,
    ...processCreateParams(params)
  });
};
var ZodSet = class _ZodSet extends ZodType {
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.set) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.set,
        received: ctx.parsedType
      });
      return INVALID;
    }
    const def = this._def;
    if (def.minSize !== null) {
      if (ctx.data.size < def.minSize.value) {
        addIssueToContext(ctx, {
          code: ZodIssueCode.too_small,
          minimum: def.minSize.value,
          type: "set",
          inclusive: true,
          exact: false,
          message: def.minSize.message
        });
        status.dirty();
      }
    }
    if (def.maxSize !== null) {
      if (ctx.data.size > def.maxSize.value) {
        addIssueToContext(ctx, {
          code: ZodIssueCode.too_big,
          maximum: def.maxSize.value,
          type: "set",
          inclusive: true,
          exact: false,
          message: def.maxSize.message
        });
        status.dirty();
      }
    }
    const valueType = this._def.valueType;
    function finalizeSet(elements2) {
      const parsedSet = /* @__PURE__ */ new Set();
      for (const element of elements2) {
        if (element.status === "aborted")
          return INVALID;
        if (element.status === "dirty")
          status.dirty();
        parsedSet.add(element.value);
      }
      return { status: status.value, value: parsedSet };
    }
    const elements = [...ctx.data.values()].map((item, i) => valueType._parse(new ParseInputLazyPath(ctx, item, ctx.path, i)));
    if (ctx.common.async) {
      return Promise.all(elements).then((elements2) => finalizeSet(elements2));
    } else {
      return finalizeSet(elements);
    }
  }
  min(minSize, message) {
    return new _ZodSet({
      ...this._def,
      minSize: { value: minSize, message: errorUtil.toString(message) }
    });
  }
  max(maxSize, message) {
    return new _ZodSet({
      ...this._def,
      maxSize: { value: maxSize, message: errorUtil.toString(message) }
    });
  }
  size(size, message) {
    return this.min(size, message).max(size, message);
  }
  nonempty(message) {
    return this.min(1, message);
  }
};
ZodSet.create = (valueType, params) => {
  return new ZodSet({
    valueType,
    minSize: null,
    maxSize: null,
    typeName: ZodFirstPartyTypeKind.ZodSet,
    ...processCreateParams(params)
  });
};
var ZodFunction = class _ZodFunction extends ZodType {
  constructor() {
    super(...arguments);
    this.validate = this.implement;
  }
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.function) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.function,
        received: ctx.parsedType
      });
      return INVALID;
    }
    function makeArgsIssue(args, error) {
      return makeIssue({
        data: args,
        path: ctx.path,
        errorMaps: [ctx.common.contextualErrorMap, ctx.schemaErrorMap, getErrorMap(), en_default].filter((x) => !!x),
        issueData: {
          code: ZodIssueCode.invalid_arguments,
          argumentsError: error
        }
      });
    }
    function makeReturnsIssue(returns, error) {
      return makeIssue({
        data: returns,
        path: ctx.path,
        errorMaps: [ctx.common.contextualErrorMap, ctx.schemaErrorMap, getErrorMap(), en_default].filter((x) => !!x),
        issueData: {
          code: ZodIssueCode.invalid_return_type,
          returnTypeError: error
        }
      });
    }
    const params = { errorMap: ctx.common.contextualErrorMap };
    const fn = ctx.data;
    if (this._def.returns instanceof ZodPromise) {
      const me = this;
      return OK(async function(...args) {
        const error = new ZodError([]);
        const parsedArgs = await me._def.args.parseAsync(args, params).catch((e) => {
          error.addIssue(makeArgsIssue(args, e));
          throw error;
        });
        const result2 = await Reflect.apply(fn, this, parsedArgs);
        const parsedReturns = await me._def.returns._def.type.parseAsync(result2, params).catch((e) => {
          error.addIssue(makeReturnsIssue(result2, e));
          throw error;
        });
        return parsedReturns;
      });
    } else {
      const me = this;
      return OK(function(...args) {
        const parsedArgs = me._def.args.safeParse(args, params);
        if (!parsedArgs.success) {
          throw new ZodError([makeArgsIssue(args, parsedArgs.error)]);
        }
        const result2 = Reflect.apply(fn, this, parsedArgs.data);
        const parsedReturns = me._def.returns.safeParse(result2, params);
        if (!parsedReturns.success) {
          throw new ZodError([makeReturnsIssue(result2, parsedReturns.error)]);
        }
        return parsedReturns.data;
      });
    }
  }
  parameters() {
    return this._def.args;
  }
  returnType() {
    return this._def.returns;
  }
  args(...items) {
    return new _ZodFunction({
      ...this._def,
      args: ZodTuple.create(items).rest(ZodUnknown.create())
    });
  }
  returns(returnType) {
    return new _ZodFunction({
      ...this._def,
      returns: returnType
    });
  }
  implement(func) {
    const validatedFunc = this.parse(func);
    return validatedFunc;
  }
  strictImplement(func) {
    const validatedFunc = this.parse(func);
    return validatedFunc;
  }
  static create(args, returns, params) {
    return new _ZodFunction({
      args: args ? args : ZodTuple.create([]).rest(ZodUnknown.create()),
      returns: returns || ZodUnknown.create(),
      typeName: ZodFirstPartyTypeKind.ZodFunction,
      ...processCreateParams(params)
    });
  }
};
var ZodLazy = class extends ZodType {
  get schema() {
    return this._def.getter();
  }
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    const lazySchema = this._def.getter();
    return lazySchema._parse({ data: ctx.data, path: ctx.path, parent: ctx });
  }
};
ZodLazy.create = (getter, params) => {
  return new ZodLazy({
    getter,
    typeName: ZodFirstPartyTypeKind.ZodLazy,
    ...processCreateParams(params)
  });
};
var ZodLiteral = class extends ZodType {
  _parse(input) {
    if (input.data !== this._def.value) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        received: ctx.data,
        code: ZodIssueCode.invalid_literal,
        expected: this._def.value
      });
      return INVALID;
    }
    return { status: "valid", value: input.data };
  }
  get value() {
    return this._def.value;
  }
};
ZodLiteral.create = (value, params) => {
  return new ZodLiteral({
    value,
    typeName: ZodFirstPartyTypeKind.ZodLiteral,
    ...processCreateParams(params)
  });
};
function createZodEnum(values, params) {
  return new ZodEnum({
    values,
    typeName: ZodFirstPartyTypeKind.ZodEnum,
    ...processCreateParams(params)
  });
}
var ZodEnum = class _ZodEnum extends ZodType {
  _parse(input) {
    if (typeof input.data !== "string") {
      const ctx = this._getOrReturnCtx(input);
      const expectedValues = this._def.values;
      addIssueToContext(ctx, {
        expected: util.joinValues(expectedValues),
        received: ctx.parsedType,
        code: ZodIssueCode.invalid_type
      });
      return INVALID;
    }
    if (!this._cache) {
      this._cache = new Set(this._def.values);
    }
    if (!this._cache.has(input.data)) {
      const ctx = this._getOrReturnCtx(input);
      const expectedValues = this._def.values;
      addIssueToContext(ctx, {
        received: ctx.data,
        code: ZodIssueCode.invalid_enum_value,
        options: expectedValues
      });
      return INVALID;
    }
    return OK(input.data);
  }
  get options() {
    return this._def.values;
  }
  get enum() {
    const enumValues = {};
    for (const val of this._def.values) {
      enumValues[val] = val;
    }
    return enumValues;
  }
  get Values() {
    const enumValues = {};
    for (const val of this._def.values) {
      enumValues[val] = val;
    }
    return enumValues;
  }
  get Enum() {
    const enumValues = {};
    for (const val of this._def.values) {
      enumValues[val] = val;
    }
    return enumValues;
  }
  extract(values, newDef = this._def) {
    return _ZodEnum.create(values, {
      ...this._def,
      ...newDef
    });
  }
  exclude(values, newDef = this._def) {
    return _ZodEnum.create(this.options.filter((opt) => !values.includes(opt)), {
      ...this._def,
      ...newDef
    });
  }
};
ZodEnum.create = createZodEnum;
var ZodNativeEnum = class extends ZodType {
  _parse(input) {
    const nativeEnumValues = util.getValidEnumValues(this._def.values);
    const ctx = this._getOrReturnCtx(input);
    if (ctx.parsedType !== ZodParsedType.string && ctx.parsedType !== ZodParsedType.number) {
      const expectedValues = util.objectValues(nativeEnumValues);
      addIssueToContext(ctx, {
        expected: util.joinValues(expectedValues),
        received: ctx.parsedType,
        code: ZodIssueCode.invalid_type
      });
      return INVALID;
    }
    if (!this._cache) {
      this._cache = new Set(util.getValidEnumValues(this._def.values));
    }
    if (!this._cache.has(input.data)) {
      const expectedValues = util.objectValues(nativeEnumValues);
      addIssueToContext(ctx, {
        received: ctx.data,
        code: ZodIssueCode.invalid_enum_value,
        options: expectedValues
      });
      return INVALID;
    }
    return OK(input.data);
  }
  get enum() {
    return this._def.values;
  }
};
ZodNativeEnum.create = (values, params) => {
  return new ZodNativeEnum({
    values,
    typeName: ZodFirstPartyTypeKind.ZodNativeEnum,
    ...processCreateParams(params)
  });
};
var ZodPromise = class extends ZodType {
  unwrap() {
    return this._def.type;
  }
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    if (ctx.parsedType !== ZodParsedType.promise && ctx.common.async === false) {
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.promise,
        received: ctx.parsedType
      });
      return INVALID;
    }
    const promisified = ctx.parsedType === ZodParsedType.promise ? ctx.data : Promise.resolve(ctx.data);
    return OK(promisified.then((data) => {
      return this._def.type.parseAsync(data, {
        path: ctx.path,
        errorMap: ctx.common.contextualErrorMap
      });
    }));
  }
};
ZodPromise.create = (schema2, params) => {
  return new ZodPromise({
    type: schema2,
    typeName: ZodFirstPartyTypeKind.ZodPromise,
    ...processCreateParams(params)
  });
};
var ZodEffects = class extends ZodType {
  innerType() {
    return this._def.schema;
  }
  sourceType() {
    return this._def.schema._def.typeName === ZodFirstPartyTypeKind.ZodEffects ? this._def.schema.sourceType() : this._def.schema;
  }
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    const effect = this._def.effect || null;
    const checkCtx = {
      addIssue: (arg) => {
        addIssueToContext(ctx, arg);
        if (arg.fatal) {
          status.abort();
        } else {
          status.dirty();
        }
      },
      get path() {
        return ctx.path;
      }
    };
    checkCtx.addIssue = checkCtx.addIssue.bind(checkCtx);
    if (effect.type === "preprocess") {
      const processed = effect.transform(ctx.data, checkCtx);
      if (ctx.common.async) {
        return Promise.resolve(processed).then(async (processed2) => {
          if (status.value === "aborted")
            return INVALID;
          const result2 = await this._def.schema._parseAsync({
            data: processed2,
            path: ctx.path,
            parent: ctx
          });
          if (result2.status === "aborted")
            return INVALID;
          if (result2.status === "dirty")
            return DIRTY(result2.value);
          if (status.value === "dirty")
            return DIRTY(result2.value);
          return result2;
        });
      } else {
        if (status.value === "aborted")
          return INVALID;
        const result2 = this._def.schema._parseSync({
          data: processed,
          path: ctx.path,
          parent: ctx
        });
        if (result2.status === "aborted")
          return INVALID;
        if (result2.status === "dirty")
          return DIRTY(result2.value);
        if (status.value === "dirty")
          return DIRTY(result2.value);
        return result2;
      }
    }
    if (effect.type === "refinement") {
      const executeRefinement = (acc) => {
        const result2 = effect.refinement(acc, checkCtx);
        if (ctx.common.async) {
          return Promise.resolve(result2);
        }
        if (result2 instanceof Promise) {
          throw new Error("Async refinement encountered during synchronous parse operation. Use .parseAsync instead.");
        }
        return acc;
      };
      if (ctx.common.async === false) {
        const inner = this._def.schema._parseSync({
          data: ctx.data,
          path: ctx.path,
          parent: ctx
        });
        if (inner.status === "aborted")
          return INVALID;
        if (inner.status === "dirty")
          status.dirty();
        executeRefinement(inner.value);
        return { status: status.value, value: inner.value };
      } else {
        return this._def.schema._parseAsync({ data: ctx.data, path: ctx.path, parent: ctx }).then((inner) => {
          if (inner.status === "aborted")
            return INVALID;
          if (inner.status === "dirty")
            status.dirty();
          return executeRefinement(inner.value).then(() => {
            return { status: status.value, value: inner.value };
          });
        });
      }
    }
    if (effect.type === "transform") {
      if (ctx.common.async === false) {
        const base = this._def.schema._parseSync({
          data: ctx.data,
          path: ctx.path,
          parent: ctx
        });
        if (!isValid(base))
          return INVALID;
        const result2 = effect.transform(base.value, checkCtx);
        if (result2 instanceof Promise) {
          throw new Error(`Asynchronous transform encountered during synchronous parse operation. Use .parseAsync instead.`);
        }
        return { status: status.value, value: result2 };
      } else {
        return this._def.schema._parseAsync({ data: ctx.data, path: ctx.path, parent: ctx }).then((base) => {
          if (!isValid(base))
            return INVALID;
          return Promise.resolve(effect.transform(base.value, checkCtx)).then((result2) => ({
            status: status.value,
            value: result2
          }));
        });
      }
    }
    util.assertNever(effect);
  }
};
ZodEffects.create = (schema2, effect, params) => {
  return new ZodEffects({
    schema: schema2,
    typeName: ZodFirstPartyTypeKind.ZodEffects,
    effect,
    ...processCreateParams(params)
  });
};
ZodEffects.createWithPreprocess = (preprocess, schema2, params) => {
  return new ZodEffects({
    schema: schema2,
    effect: { type: "preprocess", transform: preprocess },
    typeName: ZodFirstPartyTypeKind.ZodEffects,
    ...processCreateParams(params)
  });
};
var ZodOptional = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType === ZodParsedType.undefined) {
      return OK(void 0);
    }
    return this._def.innerType._parse(input);
  }
  unwrap() {
    return this._def.innerType;
  }
};
ZodOptional.create = (type, params) => {
  return new ZodOptional({
    innerType: type,
    typeName: ZodFirstPartyTypeKind.ZodOptional,
    ...processCreateParams(params)
  });
};
var ZodNullable = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType === ZodParsedType.null) {
      return OK(null);
    }
    return this._def.innerType._parse(input);
  }
  unwrap() {
    return this._def.innerType;
  }
};
ZodNullable.create = (type, params) => {
  return new ZodNullable({
    innerType: type,
    typeName: ZodFirstPartyTypeKind.ZodNullable,
    ...processCreateParams(params)
  });
};
var ZodDefault = class extends ZodType {
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    let data = ctx.data;
    if (ctx.parsedType === ZodParsedType.undefined) {
      data = this._def.defaultValue();
    }
    return this._def.innerType._parse({
      data,
      path: ctx.path,
      parent: ctx
    });
  }
  removeDefault() {
    return this._def.innerType;
  }
};
ZodDefault.create = (type, params) => {
  return new ZodDefault({
    innerType: type,
    typeName: ZodFirstPartyTypeKind.ZodDefault,
    defaultValue: typeof params.default === "function" ? params.default : () => params.default,
    ...processCreateParams(params)
  });
};
var ZodCatch = class extends ZodType {
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    const newCtx = {
      ...ctx,
      common: {
        ...ctx.common,
        issues: []
      }
    };
    const result2 = this._def.innerType._parse({
      data: newCtx.data,
      path: newCtx.path,
      parent: {
        ...newCtx
      }
    });
    if (isAsync(result2)) {
      return result2.then((result3) => {
        return {
          status: "valid",
          value: result3.status === "valid" ? result3.value : this._def.catchValue({
            get error() {
              return new ZodError(newCtx.common.issues);
            },
            input: newCtx.data
          })
        };
      });
    } else {
      return {
        status: "valid",
        value: result2.status === "valid" ? result2.value : this._def.catchValue({
          get error() {
            return new ZodError(newCtx.common.issues);
          },
          input: newCtx.data
        })
      };
    }
  }
  removeCatch() {
    return this._def.innerType;
  }
};
ZodCatch.create = (type, params) => {
  return new ZodCatch({
    innerType: type,
    typeName: ZodFirstPartyTypeKind.ZodCatch,
    catchValue: typeof params.catch === "function" ? params.catch : () => params.catch,
    ...processCreateParams(params)
  });
};
var ZodNaN = class extends ZodType {
  _parse(input) {
    const parsedType = this._getType(input);
    if (parsedType !== ZodParsedType.nan) {
      const ctx = this._getOrReturnCtx(input);
      addIssueToContext(ctx, {
        code: ZodIssueCode.invalid_type,
        expected: ZodParsedType.nan,
        received: ctx.parsedType
      });
      return INVALID;
    }
    return { status: "valid", value: input.data };
  }
};
ZodNaN.create = (params) => {
  return new ZodNaN({
    typeName: ZodFirstPartyTypeKind.ZodNaN,
    ...processCreateParams(params)
  });
};
var BRAND = Symbol("zod_brand");
var ZodBranded = class extends ZodType {
  _parse(input) {
    const { ctx } = this._processInputParams(input);
    const data = ctx.data;
    return this._def.type._parse({
      data,
      path: ctx.path,
      parent: ctx
    });
  }
  unwrap() {
    return this._def.type;
  }
};
var ZodPipeline = class _ZodPipeline extends ZodType {
  _parse(input) {
    const { status, ctx } = this._processInputParams(input);
    if (ctx.common.async) {
      const handleAsync = async () => {
        const inResult = await this._def.in._parseAsync({
          data: ctx.data,
          path: ctx.path,
          parent: ctx
        });
        if (inResult.status === "aborted")
          return INVALID;
        if (inResult.status === "dirty") {
          status.dirty();
          return DIRTY(inResult.value);
        } else {
          return this._def.out._parseAsync({
            data: inResult.value,
            path: ctx.path,
            parent: ctx
          });
        }
      };
      return handleAsync();
    } else {
      const inResult = this._def.in._parseSync({
        data: ctx.data,
        path: ctx.path,
        parent: ctx
      });
      if (inResult.status === "aborted")
        return INVALID;
      if (inResult.status === "dirty") {
        status.dirty();
        return {
          status: "dirty",
          value: inResult.value
        };
      } else {
        return this._def.out._parseSync({
          data: inResult.value,
          path: ctx.path,
          parent: ctx
        });
      }
    }
  }
  static create(a, b) {
    return new _ZodPipeline({
      in: a,
      out: b,
      typeName: ZodFirstPartyTypeKind.ZodPipeline
    });
  }
};
var ZodReadonly = class extends ZodType {
  _parse(input) {
    const result2 = this._def.innerType._parse(input);
    const freeze = (data) => {
      if (isValid(data)) {
        data.value = Object.freeze(data.value);
      }
      return data;
    };
    return isAsync(result2) ? result2.then((data) => freeze(data)) : freeze(result2);
  }
  unwrap() {
    return this._def.innerType;
  }
};
ZodReadonly.create = (type, params) => {
  return new ZodReadonly({
    innerType: type,
    typeName: ZodFirstPartyTypeKind.ZodReadonly,
    ...processCreateParams(params)
  });
};
function cleanParams(params, data) {
  const p = typeof params === "function" ? params(data) : typeof params === "string" ? { message: params } : params;
  const p2 = typeof p === "string" ? { message: p } : p;
  return p2;
}
function custom(check, _params = {}, fatal) {
  if (check)
    return ZodAny.create().superRefine((data, ctx) => {
      const r = check(data);
      if (r instanceof Promise) {
        return r.then((r2) => {
          if (!r2) {
            const params = cleanParams(_params, data);
            const _fatal = params.fatal ?? fatal ?? true;
            ctx.addIssue({ code: "custom", ...params, fatal: _fatal });
          }
        });
      }
      if (!r) {
        const params = cleanParams(_params, data);
        const _fatal = params.fatal ?? fatal ?? true;
        ctx.addIssue({ code: "custom", ...params, fatal: _fatal });
      }
      return;
    });
  return ZodAny.create();
}
var late = {
  object: ZodObject.lazycreate
};
var ZodFirstPartyTypeKind;
(function(ZodFirstPartyTypeKind2) {
  ZodFirstPartyTypeKind2["ZodString"] = "ZodString";
  ZodFirstPartyTypeKind2["ZodNumber"] = "ZodNumber";
  ZodFirstPartyTypeKind2["ZodNaN"] = "ZodNaN";
  ZodFirstPartyTypeKind2["ZodBigInt"] = "ZodBigInt";
  ZodFirstPartyTypeKind2["ZodBoolean"] = "ZodBoolean";
  ZodFirstPartyTypeKind2["ZodDate"] = "ZodDate";
  ZodFirstPartyTypeKind2["ZodSymbol"] = "ZodSymbol";
  ZodFirstPartyTypeKind2["ZodUndefined"] = "ZodUndefined";
  ZodFirstPartyTypeKind2["ZodNull"] = "ZodNull";
  ZodFirstPartyTypeKind2["ZodAny"] = "ZodAny";
  ZodFirstPartyTypeKind2["ZodUnknown"] = "ZodUnknown";
  ZodFirstPartyTypeKind2["ZodNever"] = "ZodNever";
  ZodFirstPartyTypeKind2["ZodVoid"] = "ZodVoid";
  ZodFirstPartyTypeKind2["ZodArray"] = "ZodArray";
  ZodFirstPartyTypeKind2["ZodObject"] = "ZodObject";
  ZodFirstPartyTypeKind2["ZodUnion"] = "ZodUnion";
  ZodFirstPartyTypeKind2["ZodDiscriminatedUnion"] = "ZodDiscriminatedUnion";
  ZodFirstPartyTypeKind2["ZodIntersection"] = "ZodIntersection";
  ZodFirstPartyTypeKind2["ZodTuple"] = "ZodTuple";
  ZodFirstPartyTypeKind2["ZodRecord"] = "ZodRecord";
  ZodFirstPartyTypeKind2["ZodMap"] = "ZodMap";
  ZodFirstPartyTypeKind2["ZodSet"] = "ZodSet";
  ZodFirstPartyTypeKind2["ZodFunction"] = "ZodFunction";
  ZodFirstPartyTypeKind2["ZodLazy"] = "ZodLazy";
  ZodFirstPartyTypeKind2["ZodLiteral"] = "ZodLiteral";
  ZodFirstPartyTypeKind2["ZodEnum"] = "ZodEnum";
  ZodFirstPartyTypeKind2["ZodEffects"] = "ZodEffects";
  ZodFirstPartyTypeKind2["ZodNativeEnum"] = "ZodNativeEnum";
  ZodFirstPartyTypeKind2["ZodOptional"] = "ZodOptional";
  ZodFirstPartyTypeKind2["ZodNullable"] = "ZodNullable";
  ZodFirstPartyTypeKind2["ZodDefault"] = "ZodDefault";
  ZodFirstPartyTypeKind2["ZodCatch"] = "ZodCatch";
  ZodFirstPartyTypeKind2["ZodPromise"] = "ZodPromise";
  ZodFirstPartyTypeKind2["ZodBranded"] = "ZodBranded";
  ZodFirstPartyTypeKind2["ZodPipeline"] = "ZodPipeline";
  ZodFirstPartyTypeKind2["ZodReadonly"] = "ZodReadonly";
})(ZodFirstPartyTypeKind || (ZodFirstPartyTypeKind = {}));
var instanceOfType = (cls, params = {
  message: `Input not instance of ${cls.name}`
}) => custom((data) => data instanceof cls, params);
var stringType = ZodString.create;
var numberType = ZodNumber.create;
var nanType = ZodNaN.create;
var bigIntType = ZodBigInt.create;
var booleanType = ZodBoolean.create;
var dateType = ZodDate.create;
var symbolType = ZodSymbol.create;
var undefinedType = ZodUndefined.create;
var nullType = ZodNull.create;
var anyType = ZodAny.create;
var unknownType = ZodUnknown.create;
var neverType = ZodNever.create;
var voidType = ZodVoid.create;
var arrayType = ZodArray.create;
var objectType = ZodObject.create;
var strictObjectType = ZodObject.strictCreate;
var unionType = ZodUnion.create;
var discriminatedUnionType = ZodDiscriminatedUnion.create;
var intersectionType = ZodIntersection.create;
var tupleType = ZodTuple.create;
var recordType = ZodRecord.create;
var mapType = ZodMap.create;
var setType = ZodSet.create;
var functionType = ZodFunction.create;
var lazyType = ZodLazy.create;
var literalType = ZodLiteral.create;
var enumType = ZodEnum.create;
var nativeEnumType = ZodNativeEnum.create;
var promiseType = ZodPromise.create;
var effectsType = ZodEffects.create;
var optionalType = ZodOptional.create;
var nullableType = ZodNullable.create;
var preprocessType = ZodEffects.createWithPreprocess;
var pipelineType = ZodPipeline.create;
var ostring = () => stringType().optional();
var onumber = () => numberType().optional();
var oboolean = () => booleanType().optional();
var coerce = {
  string: ((arg) => ZodString.create({ ...arg, coerce: true })),
  number: ((arg) => ZodNumber.create({ ...arg, coerce: true })),
  boolean: ((arg) => ZodBoolean.create({
    ...arg,
    coerce: true
  })),
  bigint: ((arg) => ZodBigInt.create({ ...arg, coerce: true })),
  date: ((arg) => ZodDate.create({ ...arg, coerce: true }))
};
var NEVER = INVALID;

// src/math/leanProbeSnapshot.ts
var import_node_crypto3 = __toESM(require("node:crypto"));
var import_node_fs4 = __toESM(require("node:fs"));
var import_node_path5 = __toESM(require("node:path"));
var MAX_BYTES = 8 * 1024 * 1024 * 1024;
function readLeanProbeSnapshotFile(source, checkpoint, target, buffer = Buffer.alloc(1024 * 1024)) {
  checkpoint();
  assertMathCanonicalPath(source);
  const fd = import_node_fs4.default.openSync(source, import_node_fs4.default.constants.O_RDONLY | import_node_fs4.default.constants.O_NOFOLLOW | import_node_fs4.default.constants.O_NONBLOCK);
  let output;
  try {
    const before = import_node_fs4.default.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size > BigInt(MAX_BYTES)) throw new Error("Lean probe snapshot input is invalid.");
    if (target) {
      import_node_fs4.default.mkdirSync(import_node_path5.default.dirname(target), { recursive: true, mode: 448 });
      output = import_node_fs4.default.openSync(
        target,
        import_node_fs4.default.constants.O_WRONLY | import_node_fs4.default.constants.O_CREAT | import_node_fs4.default.constants.O_EXCL,
        384
      );
      const copied = import_node_fs4.default.fstatSync(output, { bigint: true });
      if (!copied.isFile() || copied.dev === before.dev && copied.ino === before.ino)
        throw new Error("Lean probe snapshot requires an independent regular file.");
    }
    const digest3 = import_node_crypto3.default.createHash("sha256");
    let bytes = 0;
    for (let size = import_node_fs4.default.readSync(fd, buffer); size; size = import_node_fs4.default.readSync(fd, buffer)) {
      checkpoint();
      bytes += size;
      if (bytes > MAX_BYTES) throw new Error("Lean probe snapshot exceeds its byte limit.");
      digest3.update(buffer.subarray(0, size));
      if (output !== void 0) import_node_fs4.default.writeFileSync(output, buffer.subarray(0, size));
    }
    const identity = mathFileIdentity(before);
    const after = import_node_fs4.default.fstatSync(fd, { bigint: true });
    if (BigInt(bytes) !== before.size || identity !== mathFileIdentity(after) || identity !== mathFileIdentity(import_node_fs4.default.lstatSync(source, { bigint: true })))
      throw new Error("Lean probe dependency changed during snapshot creation.");
    if (output !== void 0) {
      import_node_fs4.default.futimesSync(output, Number(after.atimeNs) / 1e9, Number(after.mtimeNs) / 1e9);
      import_node_fs4.default.fchmodSync(output, 256 | Number(before.mode & BigInt(73)));
    }
    return { digest: digest3.digest("hex"), identity, bytes, mode: Number(before.mode & BigInt(511)) };
  } finally {
    if (output !== void 0) import_node_fs4.default.closeSync(output);
    import_node_fs4.default.closeSync(fd);
  }
}

// src/math/mathProofEnvironmentCache.ts
var DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT = `/var/tmp/theoremos-proof-environments-${process.getuid?.() ?? process.pid}`;
var digest = external_exports.string().regex(/^[a-f0-9]{64}$/u);
var entrySchema = external_exports.object({
  schema: external_exports.literal("deepscientist.math.proof-environment-cache.v1"),
  fingerprint: digest,
  imageName: external_exports.string().regex(/^[a-f0-9-]+\.squashfs$/u),
  imageSha256: digest,
  imageBytes: external_exports.number().int().positive(),
  metadataHash: digest,
  stats: external_exports.object({
    files: external_exports.number().int().nonnegative(),
    bytes: external_exports.number().int().nonnegative(),
    publications: external_exports.literal(1)
  })
});

// src/math/mathProofEnvironment.ts
var MATH_PROOF_ENVIRONMENT_ENV = "DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT";
var MATH_PROOF_ENVIRONMENT_SANDBOX_ENV = "DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX";
var METADATA = ".deepscientist-proof-environment.json";
var CONFIG_FILES = [
  "lean-toolchain",
  "lakefile.toml",
  "lakefile.lean",
  "lake-manifest.json",
  ".lake/package-overrides.json"
];
var hash = external_exports.string().regex(/^[a-f0-9]{64}$/u);
var statistics = external_exports.object({ files: external_exports.number().int().nonnegative(), bytes: external_exports.number().int().nonnegative(), publications: external_exports.literal(1) }).strict();
var descriptorSchema = external_exports.object({
  schema: external_exports.literal("deepscientist.math.proof-environment.v1"),
  pid: external_exports.number().int().positive(),
  rootFd: external_exports.number().int().nonnegative(),
  rootPath: external_exports.string(),
  device: external_exports.string(),
  inode: external_exports.string(),
  startTime: external_exports.string(),
  imageSha256: hash,
  imageBytes: external_exports.number().int().positive(),
  seals: external_exports.union([external_exports.literal(0), external_exports.literal(15)]),
  metadataHash: hash,
  identity: hash,
  stats: statistics,
  leaseSocket: external_exports.string().min(1),
  leaseToken: external_exports.string().min(16)
}).strict();
var sandboxMappingSchema = external_exports.object({
  schema: external_exports.literal("deepscientist.math.proof-environment-sandbox.v1"),
  identity: hash,
  rootPath: external_exports.string().startsWith("/"),
  leaseSocket: external_exports.string().startsWith("/")
}).strict();
function readSandboxMapping(descriptor, env) {
  const encoded = env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV] ?? process.env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV];
  if (!encoded) return void 0;
  const mapping = sandboxMappingSchema.parse(JSON.parse(encoded));
  return mapping.identity === descriptor.identity ? mapping : void 0;
}
var metadataSchema = external_exports.object({
  schema: external_exports.literal("deepscientist.math.proof-environment-inputs.v1"),
  sourceCacheRoot: external_exports.string(),
  config: external_exports.record(external_exports.string(), hash.nullable()),
  sourceIdentity: hash,
  stats: statistics
}).strict();
function readJsonLine(read) {
  return new Promise((resolve, reject) => {
    let text = "", settled = false;
    const finish = (error, value) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      read.signal?.removeEventListener("abort", aborted);
      read.data.off("data", data);
      read.owner.off("error", finish).off(read.end, ended);
      if (error) reject(error);
      else resolve(value);
    };
    const ended = () => finish(new Error(read.ended)), aborted = () => finish(read.aborted());
    const timer = read.timeoutMs === void 0 ? void 0 : setTimeout(() => finish(read.timedOut()), read.timeoutMs);
    const data = (chunk) => {
      text += chunk.toString();
      if (text.length > read.limit) return finish(new Error(read.invalid));
      const newline = text.indexOf("\n");
      if (newline < 0) return;
      let value;
      try {
        value = JSON.parse(text.slice(0, newline));
      } catch {
        return finish(new Error(read.invalid));
      }
      try {
        finish(void 0, read.accept(value));
      } catch (error) {
        finish(error);
      }
    };
    read.data.on("data", data);
    read.owner.on("error", finish).on(read.end, ended);
    read.signal?.addEventListener("abort", aborted, { once: true });
    if (read.signal?.aborted) aborted();
  });
}
function processStartTime(pid) {
  const value = import_node_fs5.default.readFileSync(`/proc/${pid}/stat`, "utf8");
  const fields = value.slice(value.lastIndexOf(")") + 2).trim().split(/\s+/u);
  if (!fields[19] || fields[0] === "Z") throw new Error("Sealed proof environment process is unavailable.");
  return fields[19];
}
function consumerConfiguration(config) {
  const { [".lake/package-overrides.json"]: _sourceOverride, ...consumed } = config;
  return consumed;
}
function projectConfiguration(root) {
  assertMathCanonicalPath(root);
  return Object.fromEntries(
    CONFIG_FILES.map((relative) => {
      const file = import_node_path6.default.join(root, relative);
      try {
        if (relative === "lakefile.toml" || relative === "lake-manifest.json") {
          const text = readMathFile(file, 16 * 1024 * 1024).bytes.toString("utf8");
          const { name: _name, ...configuration2 } = relative.endsWith(".toml") ? parse(text) : JSON.parse(text);
          return [relative, mathDigest(canonicalMathJson(configuration2))];
        }
        return [relative, readLeanProbeSnapshotFile(file, () => {
        }).digest];
      } catch (error) {
        if (error.code === "ENOENT") return [relative, null];
        throw error;
      }
    })
  );
}
function resolveMathProofEnvironment(projectRoot, env = process.env) {
  const encoded = env[MATH_PROOF_ENVIRONMENT_ENV];
  if (encoded === void 0) return void 0;
  const descriptor = descriptorSchema.parse(JSON.parse(encoded));
  const hostPath = `/proc/${descriptor.pid}/fd/${descriptor.rootFd}`;
  if (descriptor.rootPath !== hostPath) throw new Error("Sealed proof environment descriptor is invalid.");
  const mapping = readSandboxMapping(descriptor, env);
  const expectedPath = mapping?.rootPath ?? hostPath;
  const verify = () => {
    if (!mapping && processStartTime(descriptor.pid) !== descriptor.startTime)
      throw new Error("Sealed proof environment process identity changed.");
    const stat = import_node_fs5.default.statSync(expectedPath, { bigint: true });
    if (!stat.isDirectory() || String(stat.dev) !== descriptor.device || String(stat.ino) !== descriptor.inode)
      throw new Error("Sealed proof environment root identity changed.");
    const bytes = import_node_fs5.default.readFileSync(import_node_path6.default.join(expectedPath, METADATA));
    if (mathDigest(bytes) !== descriptor.metadataHash) throw new Error("Sealed proof environment metadata changed.");
    const metadata = metadataSchema.parse(JSON.parse(bytes.toString("utf8")));
    if (canonicalMathJson(consumerConfiguration(metadata.config)) !== canonicalMathJson(consumerConfiguration(projectConfiguration(projectRoot))))
      throw new Error("Sealed proof environment does not match the project configuration.");
    if (canonicalMathJson(metadata.stats) !== canonicalMathJson(descriptor.stats) || mathDigest(canonicalMathJson({ metadataHash: descriptor.metadataHash, imageSha256: descriptor.imageSha256 })) !== descriptor.identity)
      throw new Error("Sealed proof environment binding changed.");
  };
  verify();
  return Object.freeze({
    packagesRoot: expectedPath,
    identity: descriptor.identity,
    stats: Object.freeze(descriptor.stats),
    verify
  });
}
async function acquireMathProofEnvironmentLease(projectRoot, env = process.env, signal, deadlineAt) {
  const environment = resolveMathProofEnvironment(projectRoot, env);
  if (!environment) return void 0;
  signal?.throwIfAborted();
  if (deadlineAt !== void 0 && Date.now() >= deadlineAt)
    throw new DOMException("Proof environment lease deadline exceeded.", "TimeoutError");
  const descriptor = descriptorSchema.parse(JSON.parse(env[MATH_PROOF_ENVIRONMENT_ENV]));
  const socket = import_node_net.default.createConnection(readSandboxMapping(descriptor, env)?.leaseSocket ?? descriptor.leaseSocket);
  try {
    socket.once("connect", () => socket.write(`${JSON.stringify({ token: descriptor.leaseToken })}
`));
    await readJsonLine({
      data: socket,
      owner: socket,
      end: "close",
      limit: 1024,
      signal,
      timeoutMs: Math.max(1, Math.min(5e3, deadlineAt === void 0 ? 5e3 : deadlineAt - Date.now())),
      timedOut: () => new DOMException("Proof environment lease handshake timed out.", "TimeoutError"),
      aborted: () => new DOMException("Proof environment lease cancelled.", "AbortError"),
      ended: "Proof environment lease closed before acknowledgement.",
      invalid: "Invalid proof environment lease acknowledgement.",
      accept: (value) => {
        if (value?.ok !== true) throw new Error("Proof environment lease was rejected.");
      }
    });
    environment.verify();
    signal?.throwIfAborted();
    socket.on("error", () => {
    });
    return Object.freeze({
      packagesRoot: environment.packagesRoot,
      release: async () => {
        if (socket.destroyed) return;
        const closed = new Promise((resolve) => socket.once("close", () => resolve()));
        socket.destroy();
        await closed;
      }
    });
  } catch (error) {
    socket.destroy();
    throw error;
  }
}

// src/math/verifier.ts
var import_node_crypto4 = __toESM(require("node:crypto"));
var import_node_child_process2 = require("node:child_process");
var import_node_fs8 = __toESM(require("node:fs"));
var import_node_os3 = __toESM(require("node:os"));
var import_node_path9 = __toESM(require("node:path"));

// src/math/contracts.ts
var MATH_FOUNDATIONAL_LEAN_AXIOMS = Object.freeze([
  "Classical.choice",
  "Quot.sound",
  "choice",
  "propext"
]);
var MATH_FOUNDATIONAL_LEAN_AXIOM_SET = new Set(MATH_FOUNDATIONAL_LEAN_AXIOMS);

// src/math/legacyIdentifiers.ts
var joined = (...parts) => parts.join("");
var LEGACY_APP_NAMESPACE = joined("ai", "on", "ui");

// src/math/mathRuntimeEnvironment.ts
var import_node_fs6 = __toESM(require("node:fs"));
var import_node_os = __toESM(require("node:os"));
var import_node_path7 = __toESM(require("node:path"));
var SECRET_KEY = /(?:API[_-]?KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|PRIVATE[_-]?KEY)/iu;
var RESOLVED_ENVIRONMENT = Symbol("resolved mathematics environment");
var withoutSecrets = (source) => Object.fromEntries(Object.entries(source).filter(([key]) => !SECRET_KEY.test(key)));
var ENV_FILE_KEYS = /* @__PURE__ */ new Set([
  "DEEPSCIENTIST_LEAN_EVAL_ROOT",
  "DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT",
  "DEEPSCIENTIST_LEAN_EVAL_TOOL_MANIFEST",
  "DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS",
  "DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS",
  "DEEPSCIENTIST_MATH_SANDBOX_BACKEND",
  "DEEPSCIENTIST_MATH_SANDBOX_IMAGE",
  "DEEPSCIENTIST_MATH_ENV_FILE",
  "ELAN_HOME",
  "LAKE_HOME",
  "LEAN_PATH",
  "LEAN_SYSROOT",
  "PATH"
]);
var OPTIONAL_ENV_FILE_KEYS = /* @__PURE__ */ new Set([
  "DEEPSCIENTIST_MATH_LEAN_LOCK",
  "DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY",
  "DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT",
  "DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS",
  "DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256",
  "http_proxy",
  "https_proxy",
  "all_proxy",
  "no_proxy",
  "HTTP_PROXY",
  "HTTPS_PROXY",
  "ALL_PROXY",
  "NO_PROXY"
]);
var DEFAULT_MATHEMATICS_ENV_FILE = import_node_path7.default.join(import_node_os.default.homedir(), ".config", "deepscientist-math", "math.env");
function parseValue2(raw) {
  const value = raw.trim();
  if (value.length >= 2 && (value.startsWith('"') && value.endsWith('"') || value.startsWith("'") && value.endsWith("'"))) {
    return value.slice(1, -1);
  }
  return value;
}
function readEnvFile(file, base) {
  if (!file) return {};
  let source;
  try {
    source = import_node_fs6.default.readFileSync(file, "utf8");
  } catch (error) {
    if (error.code === "ENOENT" && !file.endsWith(".json")) return {};
    throw error;
  }
  if (file.endsWith(".json")) {
    let parsed;
    try {
      parsed = JSON.parse(source);
    } catch {
      throw new Error("Invalid mathematics environment projection");
    }
    if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) {
      throw new Error("Invalid mathematics environment projection");
    }
    const values2 = Object.entries(parsed);
    if ([...ENV_FILE_KEYS].some((key) => !Object.hasOwn(parsed, key)) || values2.some(
      ([key, value]) => !ENV_FILE_KEYS.has(key) && !OPTIONAL_ENV_FILE_KEYS.has(key) || typeof value !== "string" || key === "DEEPSCIENTIST_MATH_ENV_FILE" && value !== file
    )) {
      throw new Error("Invalid mathematics environment projection");
    }
    return Object.fromEntries(values2);
  }
  const values = {};
  for (const line of source.split(/\r?\n/u)) {
    const match = /^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?)\s*$/u.exec(line);
    if (!match || !ENV_FILE_KEYS.has(match[1]) && !OPTIONAL_ENV_FILE_KEYS.has(match[1])) continue;
    let value = parseValue2(match[2]);
    value = value.replace(/\$\{([A-Za-z_][A-Za-z0-9_]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)/gu, (_all, braced, plain) => {
      const key = String(braced || plain);
      return values[key] ?? base[key] ?? "";
    });
    values[match[1]] = value;
  }
  return values;
}
function resolveMathematicsRuntimeEnvironment(source = process.env, envFile = source.DEEPSCIENTIST_MATH_ENV_FILE?.trim() || DEFAULT_MATHEMATICS_ENV_FILE) {
  if (source[RESOLVED_ENVIRONMENT] === envFile)
    return Object.freeze({ ...withoutSecrets(source), [RESOLVED_ENVIRONMENT]: envFile });
  const defaultPath = process.platform === "linux" ? "/usr/bin:/bin" : "";
  const values = readEnvFile(envFile, { ...source, PATH: source.PATH ?? defaultPath });
  const merged = envFile.endsWith(".json") ? { ...source, ...values, DEEPSCIENTIST_MATH_ENV_FILE: envFile } : { ...values, ...source };
  if (envFile.endsWith(".json")) {
    for (const key of OPTIONAL_ENV_FILE_KEYS) if (!Object.hasOwn(values, key)) delete merged[key];
  }
  if (values.PATH) merged.PATH = values.PATH;
  const pathEntries = [
    merged.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT && import_node_path7.default.join(merged.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT, "bin"),
    merged.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT,
    merged.ELAN_HOME && import_node_path7.default.join(merged.ELAN_HOME, "bin")
  ].filter((entry) => Boolean(entry));
  if (pathEntries.length || process.platform === "linux") {
    const basePath = merged.PATH ?? defaultPath;
    merged.PATH = [...pathEntries, ...basePath.split(import_node_path7.default.delimiter), ...process.platform === "linux" ? ["/usr/sbin"] : []].filter(Boolean).filter((entry, index, entries) => entries.indexOf(entry) === index).join(import_node_path7.default.delimiter);
  }
  return Object.freeze({ ...withoutSecrets(merged), [RESOLVED_ENVIRONMENT]: envFile });
}

// src/math/concurrency.ts
function createMathOperationLimiter(capacity) {
  let active = 0;
  const waiters = /* @__PURE__ */ new Set();
  return async (operation, signal) => {
    signal?.throwIfAborted();
    if (active < capacity() && waiters.size === 0) active++;
    else await new Promise((resolve, reject) => {
      const waiter = { resolve, signal, onAbort: () => {
        waiters.delete(waiter);
        reject(signal.reason);
      } };
      waiters.add(waiter);
      signal?.addEventListener("abort", waiter.onAbort, { once: true });
    });
    try {
      signal?.throwIfAborted();
      return await operation();
    } finally {
      active--;
      for (const waiter of waiters) {
        if (active >= capacity()) break;
        waiters.delete(waiter);
        waiter.signal?.removeEventListener("abort", waiter.onAbort);
        active++;
        waiter.resolve();
      }
    }
  };
}

// src/math/fixedLeanDependencies.ts
var import_node_fs7 = __toESM(require("node:fs"));
var import_node_os2 = __toESM(require("node:os"));
var import_node_path8 = __toESM(require("node:path"));
var outputs = (module2) => {
  const output = `.lake/build/lib/lean/${import_node_path8.default.posix.relative(module2.sourceRoot, module2.file).replace(/\.lean$/u, ".olean")}`;
  return [output, output + ".private", output + ".server", output.replace(/\.olean$/u, ".ir"), output.replace(/\.olean$/u, ".ir.sig")];
};
function snapshot(input) {
  if (!input.modules.length || input.env.LEAN_PATH?.trim() || input.env.LEAN_SYSROOT?.trim()) return;
  if (!import_node_fs7.default.existsSync(import_node_path8.default.join(input.projectRoot, "lakefile.toml")) || import_node_fs7.default.existsSync(import_node_path8.default.join(input.projectRoot, "lakefile.lean"))) return;
  const sealed = resolveMathProofEnvironment(input.projectRoot, input.env), tools = input.toolIdentity(input.projectRoot);
  if (!sealed || !tools) return;
  const closure = mathLocalModuleBuildOrder(input.projectRoot, input.modules.map((module2) => module2.file));
  if (canonicalMathJson(closure) !== canonicalMathJson(input.modules)) return;
  const sources = input.modules.map((module2) => {
    const bytes = readMathFile(import_node_path8.default.join(input.projectRoot, module2.file)).bytes;
    if (mathDigest(bytes) !== input.trustedFiles[module2.file]) throw new Error("math_fixed_dependency_source_not_trusted");
    return { ...module2, bytes, sha256: mathDigest(bytes) };
  });
  const files = sources.flatMap(outputs);
  if (new Set(files).size !== files.length) return;
  const configuration2 = LAKE_CONFIGURATION_FILES.filter((file) => file !== ".lake/package-overrides.json").map((file) => {
    try {
      return { file, bytes: readMathFile(import_node_path8.default.join(input.projectRoot, file)).bytes };
    } catch (error) {
      if (error.code === "ENOENT") return { file, bytes: null };
      throw error;
    }
  });
  const environment = Object.fromEntries([
    "PATH",
    "LANG",
    "LC_ALL",
    "ELAN_HOME",
    "LAKE_HOME",
    "LEAN_PATH",
    "LEAN_SYSROOT",
    "DEEPSCIENTIST_MATH_SANDBOX_BACKEND",
    "DEEPSCIENTIST_MATH_SANDBOX_IMAGE",
    "DEEPSCIENTIST_TEST_LEAN_AXIOMS"
  ].map((name) => [name, input.env[name] ?? null]));
  const key = mathDigest(canonicalMathJson({
    schema: "theorem-os.fixed-lean-dependencies.v1",
    profile: "sealed-dependency-only;lean-j1-R-o;no-target-sources",
    packages: sealed.identity,
    tools,
    environment,
    configuration: configuration2.map(({ file, bytes }) => [file, bytes && mathDigest(bytes)]),
    sources: sources.map(({ file, sourceRoot, module: module2, sha256 }) => ({ file, sourceRoot, module: module2, sha256 }))
  }));
  return { key, sources, configuration: configuration2 };
}
var FixedLeanDependencyCache = class {
  constructor(maxBytes = 512 * 1024 * 1024) {
    this.maxBytes = maxBytes;
  }
  entries = /* @__PURE__ */ new Map();
  root;
  bytes = 0;
  cleanup = () => {
    if (this.root) import_node_fs7.default.rmSync(this.root, { recursive: true, force: true });
  };
  dispose() {
    this.cleanup();
    this.root = void 0;
    this.entries.clear();
    this.bytes = 0;
    process.off("exit", this.cleanup);
  }
  directory() {
    if (!this.root) {
      this.root = import_node_fs7.default.realpathSync(import_node_fs7.default.mkdtempSync(import_node_path8.default.join(import_node_os2.default.tmpdir(), "math-fixed-dependencies-")));
      import_node_fs7.default.chmodSync(this.root, 448);
      process.once("exit", this.cleanup);
    }
    return import_node_fs7.default.mkdtempSync(import_node_path8.default.join(this.root, "entry-"));
  }
  restore(entry, project) {
    const files = entry.artifacts.map((artifact) => {
      if (artifact.sha256 === null) return { ...artifact, data: null };
      const data = readMathFile(import_node_path8.default.join(entry.directory, artifact.file), artifact.bytes).bytes;
      if (data.length !== artifact.bytes || mathDigest(data) !== artifact.sha256) throw new Error("math_fixed_dependency_artifact_changed");
      return { ...artifact, data };
    });
    for (const { file, data } of files) {
      const output = import_node_path8.default.join(project, file);
      assertMathCanonicalPath(output);
      if (data) {
        import_node_fs7.default.mkdirSync(import_node_path8.default.dirname(output), { recursive: true });
        import_node_fs7.default.writeFileSync(output, data, { mode: 384 });
      } else import_node_fs7.default.rmSync(output, { force: true });
    }
  }
  clearRestored(input) {
    for (const file of input.modules.flatMap(outputs)) {
      const output = import_node_path8.default.join(input.projectRoot, file);
      assertMathCanonicalPath(import_node_path8.default.dirname(output));
      import_node_fs7.default.rmSync(output, { force: true });
    }
  }
  async prepare(input, compile) {
    input.signal?.throwIfAborted();
    let before;
    try {
      before = snapshot(input);
    } catch {
      return;
    }
    if (!before) return;
    const cached = this.entries.get(before.key);
    if (cached) {
      try {
        this.restore(cached, input.projectRoot);
        if (snapshot(input)?.key !== before.key) {
          this.clearRestored(input);
          return;
        }
        this.entries.delete(before.key);
        this.entries.set(before.key, cached);
        return { kind: "ready", hit: true, stdout: cached.stdout, stderr: cached.stderr, durationMs: 0 };
      } catch {
        try {
          this.clearRestored(input);
        } catch {
        }
        this.entries.delete(before.key);
        this.bytes -= cached.bytes;
        try {
          import_node_fs7.default.rmSync(cached.directory, { recursive: true, force: true });
        } catch {
        }
      }
    }
    let directory, retained = false, restoring = false;
    try {
      directory = this.directory();
      const project = import_node_path8.default.join(directory, "project");
      for (const { file, bytes } of [...before.configuration, ...before.sources]) if (bytes) {
        const output = import_node_path8.default.join(project, file);
        import_node_fs7.default.mkdirSync(import_node_path8.default.dirname(output), { recursive: true });
        import_node_fs7.default.writeFileSync(output, bytes);
      }
      const result2 = await compile(project);
      input.signal?.throwIfAborted();
      if (result2.exitCode !== 0 || result2.timedOut || result2.aborted || !result2.started || result2.errorCode) return { kind: "failed", result: result2 };
      if (snapshot(input)?.key !== before.key || snapshot({ ...input, projectRoot: project })?.key !== before.key) return;
      const artifacts = [];
      for (const module2 of input.modules) for (const file of outputs(module2)) {
        try {
          const source = import_node_path8.default.join(project, file);
          assertMathCanonicalPath(source);
          const data = readMathFile(source).bytes;
          const output = import_node_path8.default.join(directory, file);
          import_node_fs7.default.mkdirSync(import_node_path8.default.dirname(output), { recursive: true });
          import_node_fs7.default.writeFileSync(output, data, { mode: 256 });
          artifacts.push({ file, sha256: mathDigest(data), bytes: data.length });
        } catch (error) {
          if (error.code !== "ENOENT" || file.endsWith(".olean")) throw error;
          artifacts.push({ file, sha256: null, bytes: 0 });
        }
      }
      const entry = { directory, artifacts, bytes: artifacts.reduce((sum, item) => sum + item.bytes, 0), stdout: result2.stdout, stderr: result2.stderr };
      restoring = true;
      this.restore(entry, input.projectRoot);
      if (snapshot(input)?.key !== before.key) {
        this.clearRestored(input);
        return;
      }
      import_node_fs7.default.rmSync(project, { recursive: true, force: true });
      if (entry.bytes <= this.maxBytes) {
        const replaced = this.entries.get(before.key);
        if (replaced) {
          this.entries.delete(before.key);
          this.bytes -= replaced.bytes;
          import_node_fs7.default.rmSync(replaced.directory, { recursive: true, force: true });
        }
        while (this.entries.size && this.bytes + entry.bytes > this.maxBytes) {
          const [key, oldest] = this.entries.entries().next().value;
          this.entries.delete(key);
          this.bytes -= oldest.bytes;
          import_node_fs7.default.rmSync(oldest.directory, { recursive: true, force: true });
        }
        this.entries.set(before.key, entry);
        this.bytes += entry.bytes;
        retained = true;
      }
      return { kind: "ready", hit: false, stdout: entry.stdout, stderr: entry.stderr, durationMs: result2.durationMs };
    } catch (error) {
      if (input.signal?.aborted) throw error;
      if (restoring) try {
        this.clearRestored(input);
      } catch {
      }
      return;
    } finally {
      if (!retained && directory) try {
        import_node_fs7.default.rmSync(directory, { recursive: true, force: true });
      } catch {
      }
    }
  }
};
var fixedLeanDependencyCache = new FixedLeanDependencyCache();

// src/math/verifier.ts
var MAX_PROOF_BYTES = 16 * 1024 * 1024;
var MAX_SANDBOX_STDIN_BYTES = 64 * 1024;
var MAX_OFFICIAL_MANIFEST_BYTES = 1 * 1024 * 1024;
var DEFAULT_CONCURRENT_VERIFICATIONS = 4;
var MAX_CONCURRENT_VERIFICATIONS = 16;
var DEFAULT_TIMEOUT_MS = 10 * 60 * 1e3;
var MAX_TIMEOUT_MS = 24 * 60 * 60 * 1e3;
var DEFAULT_BATCH_TIMEOUT_MS = 60 * 60 * 1e3;
var MAX_BATCH_TIMEOUT_MS = 24 * 60 * 60 * 1e3;
var DEFAULT_OFFICIAL_TIMEOUT_MS = 60 * 60 * 1e3;
var MAX_OFFICIAL_TIMEOUT_MS = 24 * 60 * 60 * 1e3;
var configuredVerificationConcurrency = () => {
  const configured = Number.parseInt(process.env.DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY || "", 10);
  if (!Number.isFinite(configured)) return DEFAULT_CONCURRENT_VERIFICATIONS;
  return Math.max(1, Math.min(MAX_CONCURRENT_VERIFICATIONS, configured));
};
var fingerprintMetadataTree = (candidate, maxEntries = 5e4) => {
  const digest3 = import_node_crypto4.default.createHash("sha256");
  let entries = 0;
  const visit = (absolutePath, relativePath) => {
    if (entries++ >= maxEntries) {
      digest3.update(`truncated\0${relativePath}\0`);
      return;
    }
    let stat;
    try {
      stat = import_node_fs8.default.lstatSync(absolutePath);
    } catch {
      digest3.update(`missing\0${relativePath}\0`);
      return;
    }
    digest3.update(`entry\0${relativePath}\0${stat.mode}\0${stat.size}\0${stat.mtimeMs}\0`);
    if (!stat.isDirectory() || stat.isSymbolicLink()) return;
    for (const entry of import_node_fs8.default.readdirSync(absolutePath, { withFileTypes: true }).toSorted((left, right) => left.name.localeCompare(right.name))) {
      visit(import_node_path9.default.join(absolutePath, entry.name), import_node_path9.default.posix.join(relativePath, entry.name));
    }
  };
  visit(candidate, ".");
  return digest3.digest("hex");
};
var readPackageGitIdentity = (packageRoot) => {
  try {
    let gitDirectory = import_node_path9.default.join(packageRoot, ".git");
    if (import_node_fs8.default.existsSync(gitDirectory) && import_node_fs8.default.statSync(gitDirectory).isFile()) {
      const match = /^gitdir:\s*(.+)\s*$/im.exec(import_node_fs8.default.readFileSync(gitDirectory, "utf8"));
      if (match) gitDirectory = import_node_path9.default.resolve(packageRoot, match[1]);
    }
    if (!import_node_fs8.default.statSync(gitDirectory).isDirectory()) return void 0;
    const head = import_node_fs8.default.readFileSync(import_node_path9.default.join(gitDirectory, "HEAD"), "utf8").trim();
    const ref = /^ref:\s*(.+)$/u.exec(head)?.[1];
    const revision = ref ? import_node_fs8.default.existsSync(import_node_path9.default.join(gitDirectory, ref)) ? import_node_fs8.default.readFileSync(import_node_path9.default.join(gitDirectory, ref), "utf8").trim() : head : head;
    const index = import_node_path9.default.join(gitDirectory, "index");
    const indexStat = import_node_fs8.default.existsSync(index) ? import_node_fs8.default.statSync(index) : void 0;
    return `${revision}|dirty-marker:${indexStat ? `${indexStat.size}:${indexStat.mtimeMs}` : "none"}|tree-marker:${fingerprintMetadataTree(packageRoot, 8192)}`;
  } catch {
    return void 0;
  }
};
var fingerprintVerifierDependency = (candidate) => {
  try {
    const stat = import_node_fs8.default.statSync(candidate);
    if (!stat.isFile()) return fingerprintMetadataTree(candidate, 8192);
    const descriptor = import_node_fs8.default.openSync(candidate, "r");
    try {
      const digest3 = import_node_crypto4.default.createHash("sha256"), buffer = Buffer.allocUnsafe(1024 * 1024);
      let bytes;
      while ((bytes = import_node_fs8.default.readSync(descriptor, buffer, 0, buffer.length, null)) > 0)
        digest3.update(buffer.subarray(0, bytes));
      return digest3.digest("hex");
    } finally {
      import_node_fs8.default.closeSync(descriptor);
    }
  } catch {
    return fingerprintMetadataTree(candidate, 8192);
  }
};
var executableOnPath = (name, source = process.env.PATH || "") => {
  for (const entry of source.split(import_node_path9.default.delimiter).filter(Boolean)) {
    const candidate = import_node_path9.default.join(entry, name);
    try {
      if (import_node_fs8.default.statSync(candidate).isFile()) return candidate;
    } catch {
    }
  }
  return void 0;
};
var resolveCommandForFingerprint = (command, env) => {
  const requested = command.trim();
  if (!requested) return void 0;
  return import_node_path9.default.isAbsolute(requested) ? requested : executableOnPath(requested, env?.PATH || process.env.PATH || "");
};
var withinProject = (projectRoot, candidate) => {
  const root = import_node_path9.default.resolve(projectRoot);
  const resolved = import_node_path9.default.resolve(candidate);
  return resolved === root || resolved.startsWith(`${root}${import_node_path9.default.sep}`);
};
var canonicalProjectRoot = (projectRoot) => {
  const resolved = import_node_path9.default.resolve(projectRoot);
  let canonical;
  try {
    canonical = import_node_fs8.default.realpathSync(resolved);
  } catch (error) {
    throw new Error(
      `The project root could not be canonicalized: ${error instanceof Error ? error.message : String(error)}`,
      {
        cause: error
      }
    );
  }
  if (!import_node_fs8.default.statSync(canonical).isDirectory()) throw new Error("The project root must be a directory.");
  return canonical;
};
var resolveLakePackagesCaches = (projectRoot, env = process.env) => {
  const trustedRoots = [];
  const addTrustedRoot = (root) => {
    try {
      const canonical = import_node_fs8.default.realpathSync(root);
      if (import_node_fs8.default.statSync(canonical).isDirectory() && !trustedRoots.includes(canonical)) trustedRoots.push(canonical);
    } catch {
    }
  };
  addTrustedRoot(projectRoot);
  for (const value of (env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || "").split(import_node_path9.default.delimiter)) {
    const root = value.trim();
    if (root) addTrustedRoot(root);
  }
  const candidates = [import_node_path9.default.join(projectRoot, ".lake", "packages"), ...trustedRoots.slice(1)];
  const resolved = [];
  for (const candidate of candidates) {
    try {
      const canonical = import_node_fs8.default.realpathSync(candidate);
      if (!import_node_fs8.default.statSync(canonical).isDirectory()) continue;
      if (trustedRoots.some((root) => withinProject(root, canonical))) resolved.push(canonical);
    } catch {
    }
  }
  return [...new Set(resolved)];
};
var resolveVerifiedLakePackagesCache = (sourceProjectRoot, targetProjectRoot, env = process.env) => {
  const sealed = resolveMathProofEnvironment(targetProjectRoot, env);
  if (sealed) return sealed.packagesRoot;
  for (const packagesRoot of resolveLakePackagesCaches(sourceProjectRoot, env)) {
    const verified = verifyLakePackagesCache(packagesRoot, targetProjectRoot);
    if (verified) return verified;
  }
  return void 0;
};
var verifyLakePackagesCache = (packagesRoot, targetProjectRoot) => {
  try {
    const manifest = JSON.parse(import_node_fs8.default.readFileSync(import_node_path9.default.join(targetProjectRoot, "lake-manifest.json"), "utf8"));
    const packages = Array.isArray(manifest.packages) ? manifest.packages : [];
    if (!packages.length) return void 0;
    for (const item of packages) {
      if (!item || typeof item !== "object") return void 0;
      const record = item;
      const name = typeof record.name === "string" ? record.name : "";
      const git = record.git && typeof record.git === "object" ? record.git : record;
      const revision = [git.rev, git.commit, git.revision].find((value) => typeof value === "string");
      if (!name || !revision || !/^[0-9a-f]{7,64}$/u.test(revision)) return void 0;
      const packageDirectory = [name, name.replace(/^«(.+)»$/u, "$1")].find(
        (candidate) => import_node_fs8.default.existsSync(import_node_path9.default.join(packagesRoot, candidate))
      );
      if (!packageDirectory) return void 0;
      const packageRoot = assertNoSymlinkTraversal(
        packagesRoot,
        import_node_path9.default.join(packagesRoot, packageDirectory),
        `Lake package ${name}`
      );
      const identity = readPackageGitIdentity(packageRoot);
      const actualRevision = identity?.split("|", 1)[0] || "";
      if (!actualRevision || !actualRevision.toLowerCase().startsWith(revision.toLowerCase())) {
        return void 0;
      }
    }
    return packagesRoot;
  } catch {
    return void 0;
  }
};
var BWRAP_RESERVED_ROOTS = [
  "/usr",
  "/bin",
  "/sbin",
  "/lib",
  "/lib64",
  "/etc",
  "/workspace",
  "/tmp",
  "/proc",
  "/dev",
  "/sys",
  "/run",
  "/toolchains",
  "/runtime"
];
var ensureLakePackagesMountPoint = (projectRoot, checkoutRoot) => {
  const packages = import_node_path9.default.join(import_node_path9.default.resolve(projectRoot), ".lake", "packages");
  const link = import_node_fs8.default.lstatSync(packages, { throwIfNoEntry: false });
  if (link?.isSymbolicLink()) {
    const target = import_node_fs8.default.realpathSync(packages);
    const checkout = import_node_fs8.default.realpathSync(checkoutRoot);
    if (!import_node_path9.default.isAbsolute(target) || target.split(import_node_path9.default.sep).filter(Boolean).length < 2 || !import_node_fs8.default.statSync(target).isDirectory() || target === checkout || target.startsWith(`${checkout}${import_node_path9.default.sep}`) || BWRAP_RESERVED_ROOTS.some((root) => target === root || root !== "/tmp" && target.startsWith(`${root}/`))) {
      throw new Error("Lean sandbox Lake package mount target must be a regular directory.");
    }
    return target;
  }
  let current = import_node_path9.default.resolve(projectRoot);
  for (const segment of [".lake", "packages"]) {
    current = import_node_path9.default.join(current, segment);
    try {
      const stat = import_node_fs8.default.lstatSync(current);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error("Lean sandbox Lake package mount target must be a regular directory.");
      }
    } catch (error) {
      if (error.code !== "ENOENT") throw error;
      import_node_fs8.default.mkdirSync(current, { recursive: false, mode: 448 });
    }
  }
  return void 0;
};
var resolveMathematicsLakePackagesCache = (projectRoot, env = process.env) => resolveVerifiedLakePackagesCache(projectRoot, projectRoot, env);
var assertNoSymlinkTraversal = (root, target, field, canonicalRoot = canonicalProjectRoot(root)) => {
  const lexicalTarget = import_node_path9.default.resolve(target);
  const lexicalRelative = import_node_path9.default.relative(import_node_path9.default.resolve(root), lexicalTarget);
  if (lexicalRelative.startsWith("..") || import_node_path9.default.isAbsolute(lexicalRelative)) {
    throw new Error(`${field} must remain inside the bound project root.`);
  }
  let cursor = import_node_path9.default.resolve(root);
  for (const segment of lexicalRelative.split(import_node_path9.default.sep).filter(Boolean)) {
    cursor = import_node_path9.default.join(cursor, segment);
    if (import_node_fs8.default.lstatSync(cursor).isSymbolicLink()) {
      throw new Error(`${field} must not traverse a symbolic link.`);
    }
  }
  let canonicalTarget;
  try {
    canonicalTarget = import_node_fs8.default.realpathSync(lexicalTarget);
  } catch (error) {
    throw new Error(`${field} could not be canonicalized: ${error instanceof Error ? error.message : String(error)}`, {
      cause: error
    });
  }
  if (!withinProject(canonicalRoot, canonicalTarget)) {
    throw new Error(`${field} must resolve inside the bound project root.`);
  }
  return canonicalTarget;
};
var withVerificationSlot = createMathOperationLimiter(configuredVerificationConcurrency);
var withLeanProcessSlot = createMathOperationLimiter(configuredVerificationConcurrency);
var OFFICIAL_EXECUTABLE_ALLOWLIST = /* @__PURE__ */ new Set([
  "lake",
  "lean",
  "elan",
  "python",
  "python3",
  "pytest",
  "uv",
  "cargo",
  "grep",
  "test"
]);
var officialComparatorEnvironment = (source) => {
  const input = source || process.env;
  const allowed = ["PATH", "LANG", "LC_ALL"];
  const environment = {};
  for (const key of allowed) {
    const value = input[key];
    if (value) environment[key] = value;
  }
  return environment;
};
var linkedLeanToolchain = (pathEntries) => {
  for (const entry of pathEntries) {
    const lake = import_node_path9.default.join(entry, "lake");
    try {
      if (!import_node_fs8.default.lstatSync(lake).isSymbolicLink()) continue;
      const real = import_node_fs8.default.realpathSync(lake);
      if (import_node_path9.default.basename(real) !== "lake" || import_node_path9.default.basename(import_node_path9.default.dirname(real)) !== "bin") continue;
      const toolchain = import_node_path9.default.dirname(import_node_path9.default.dirname(real));
      if (import_node_fs8.default.statSync(import_node_path9.default.join(toolchain, "bin", "elan"), { throwIfNoEntry: false })?.isFile() || import_node_fs8.default.statSync(import_node_path9.default.join(toolchain, "bin", "lean")).isFile() && import_node_fs8.default.statSync(import_node_path9.default.join(toolchain, "lib", "lean")).isDirectory())
        return toolchain;
    } catch {
    }
  }
  return void 0;
};
var resolveTrustedElanHome = (source) => {
  const configured = source?.DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS || process.env.DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS;
  const requested = source?.ELAN_HOME || process.env.ELAN_HOME;
  const explicitCandidates = [
    ...requested ? [requested] : [],
    ...(configured || "").split(import_node_path9.default.delimiter).filter(Boolean)
  ];
  const candidates = [...explicitCandidates];
  if (!candidates.length) {
    const pathEntries2 = (source?.PATH || process.env.PATH || "").split(import_node_path9.default.delimiter).filter(Boolean);
    const linked = linkedLeanToolchain(pathEntries2);
    if (linked) return linked;
    for (const entry of pathEntries2) {
      if (import_node_path9.default.basename(entry) === "bin") candidates.push(import_node_path9.default.dirname(entry));
    }
  }
  for (const candidate of candidates) {
    const resolved = import_node_path9.default.resolve(candidate);
    if (!import_node_fs8.default.existsSync(resolved)) continue;
    try {
      const canonical = import_node_fs8.default.realpathSync(resolved);
      if (!import_node_fs8.default.statSync(canonical).isDirectory()) continue;
      if (import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "bin", "elan")) || (import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "bin", "lean")) || import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "bin", "lake"))) && import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "lib", "lean"))) {
        return canonical;
      }
    } catch {
    }
  }
  const pathEntries = (source?.PATH || process.env.PATH || "").split(import_node_path9.default.delimiter).filter(Boolean);
  if (pathEntries.some((entry) => import_node_fs8.default.existsSync(import_node_path9.default.join(entry, "lean")) || import_node_fs8.default.existsSync(import_node_path9.default.join(entry, "lake")))) {
    return linkedLeanToolchain(pathEntries) ?? "";
  }
  const processLinked = linkedLeanToolchain((process.env.PATH || "").split(import_node_path9.default.delimiter).filter(Boolean));
  if (processLinked) return processLinked;
  const defaultHome = import_node_path9.default.join(import_node_os3.default.homedir(), ".elan");
  try {
    const canonical = import_node_fs8.default.realpathSync(defaultHome);
    if (import_node_fs8.default.statSync(canonical).isDirectory() && (import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "bin", "lean")) || import_node_fs8.default.existsSync(import_node_path9.default.join(canonical, "bin", "lake")))) {
      return canonical;
    }
  } catch {
  }
  return "";
};
var resolveTrustedToolchainBin = (projectRoot, projectRelative, source, elanHome) => {
  if (!elanHome) return "";
  const elan = import_node_path9.default.join(elanHome, "bin", "elan");
  if (!import_node_fs8.default.existsSync(elan)) {
    try {
      return import_node_fs8.default.statSync(import_node_path9.default.join(elanHome, "bin", "lake")).isFile() && import_node_fs8.default.statSync(import_node_path9.default.join(elanHome, "bin", "lean")).isFile() && import_node_fs8.default.statSync(import_node_path9.default.join(elanHome, "lib", "lean")).isDirectory() ? import_node_path9.default.join(elanHome, "bin") : "";
    } catch {
      return "";
    }
  }
  const result2 = (0, import_node_child_process2.spawnSync)(elan, ["which", "lean"], {
    cwd: import_node_path9.default.join(projectRoot, projectRelative),
    env: { ...process.env, ...source, ELAN_HOME: elanHome },
    encoding: "utf8",
    timeout: 2e3
  });
  if (result2.status !== 0) return "";
  const leanPath = result2.stdout.trim();
  if (!import_node_path9.default.isAbsolute(leanPath) || import_node_path9.default.basename(leanPath) !== "lean") return "";
  try {
    const resolved = import_node_fs8.default.realpathSync(leanPath);
    const bin = import_node_path9.default.dirname(resolved);
    return import_node_fs8.default.statSync(import_node_path9.default.join(bin, "lake")).isFile() ? bin : "";
  } catch {
    return "";
  }
};
function formalVerificationToolIdentity(projectRoot, env) {
  try {
    if ((env.PATH ?? process.env.PATH ?? "").split(import_node_path9.default.delimiter).some((directory) => !import_node_path9.default.isAbsolute(directory))) return void 0;
    const fingerprint2 = (file) => {
      const canonical = import_node_fs8.default.realpathSync(file), stat = import_node_fs8.default.statSync(canonical);
      if (!stat.isFile() || (stat.mode & 73) === 0) throw new Error("unavailable-tool");
      return [canonical, fingerprintVerifierDependency(canonical)];
    };
    const commands = ["lean", "lake"].map((command) => {
      const executable = resolveCommandForFingerprint(command, env);
      return [command, executable ? fingerprint2(executable) : null];
    });
    const elanHome = resolveTrustedElanHome(env);
    const bin = resolveTrustedToolchainBin(projectRoot, ".", env, elanHome);
    if (elanHome && !bin || !bin && commands.some(([, executable]) => !executable)) return void 0;
    const selected = bin ? ["lean", "lake"].map((command) => fingerprint2(import_node_path9.default.join(bin, command))) : [];
    return mathDigest(JSON.stringify({ commands, selected }));
  } catch {
    return void 0;
  }
}
var LEAN_SANDBOX_ADDRESS_SPACE_KB = 32 * 1024 * 1024;
var LEAN_SANDBOX_PROCESS_LIMIT = 4096;
var LEAN_SANDBOX_SCRIPT = String.raw`
root=$1
candidate=$2
project_relative=$3
toolchain=$4
toolchain_bin=$5
runtime=$6
counter=$7
axioms=$8
packages=$9
shift 9
overrides=$1
shift
mount --make-rprivate /
ulimit -v ${LEAN_SANDBOX_ADDRESS_SPACE_KB} 2>/dev/null || true
ulimit -u ${LEAN_SANDBOX_PROCESS_LIMIT} 2>/dev/null || true
ulimit -n 4096 2>/dev/null || true
mount --bind /usr "$root/usr"
mount -o remount,bind,ro "$root/usr"
mount --bind "$candidate" "$root/workspace"
mount -t tmpfs -o mode=755,nosuid,noexec tmpfs "$root/dev"
for device in null zero full random urandom; do
  touch "$root/dev/$device"
  mount --bind "/dev/$device" "$root/dev/$device"
done
if [ -n "$packages" ]; then
  cache_target="$root/workspace"
  if [ -n "$project_relative" ]; then cache_target="$cache_target/$project_relative"; fi
  mkdir -p "$cache_target/.lake/packages"
  mount --bind "$packages" "$cache_target/.lake/packages"
  mount -o remount,bind,ro "$cache_target/.lake/packages"
fi
if [ -n "$overrides" ]; then
  override_target="$root/workspace"
  if [ -n "$project_relative" ]; then override_target="$override_target/$project_relative"; fi
  mount --bind "$overrides" "$override_target/.lake/package-overrides.json"
  mount -o remount,bind,ro "$override_target/.lake/package-overrides.json"
fi
if [ -n "$toolchain" ]; then
  mount --bind "$toolchain" "$root/toolchains/elan"
  mount -o remount,bind,ro "$root/toolchains/elan"
fi
if [ -n "$runtime" ]; then
  mkdir -p "$root/runtime/node"
  mount --bind "$runtime" "$root/runtime/node"
  mount -o remount,bind,ro "$root/runtime/node"
fi
mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs "$root/tmp"
mount -t proc -o nosuid,nodev,noexec proc "$root/proc"
if [ -n "$project_relative" ]; then
  sandbox_cwd=/workspace/$project_relative
else
  sandbox_cwd=/workspace
fi
if [ -z "$toolchain_bin" ]; then toolchain_bin=/toolchains/elan/bin; fi
exec chroot "$root" /usr/bin/env -i \
  PATH=/runtime/node:/runtime/node/bin:$toolchain_bin:/usr/local/bin:/usr/bin:/bin \
  HOME=/tmp TMPDIR=/tmp LANG=C.UTF-8 ELAN_HOME=/toolchains/elan LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=8192 \
  DEEPSCIENTIST_TEST_LEAN_COUNTER="$counter" \
  DEEPSCIENTIST_TEST_LEAN_AXIOMS="$axioms" \
  /usr/bin/env --chdir="$sandbox_cwd" "$@"
`;
var unavailableProcessResult = (message) => ({
  started: false,
  exitCode: null,
  signal: null,
  stdout: "",
  stderr: message,
  stdoutSha256: mathDigest(""),
  stderrSha256: mathDigest(message),
  timedOut: false,
  aborted: false,
  errorCode: "SANDBOX_UNAVAILABLE",
  errorMessage: message,
  durationMs: 0
});
function inspectMathematicsSandboxBackends(env = process.env) {
  const pinnedImage = /@sha256:[0-9a-f]{64}$/iu.test(env.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || "");
  const candidates = process.platform !== "linux" ? [] : ["unshare", "bwrap", ...pinnedImage ? ["docker", "podman"] : []];
  const available = candidates.filter((kind) => executableOnPath(kind, env.PATH));
  const configured = env.DEEPSCIENTIST_MATH_SANDBOX_BACKEND;
  const preferred = configured && available.includes(configured) ? configured : pinnedImage && available.find((backend) => backend === "docker" || backend === "podman") || available[0];
  return Object.freeze({
    available: Object.freeze(available),
    ...preferred ? { preferred } : {},
    ...!available.length ? { reason: pinnedImage ? "No supported Linux sandbox backend is installed." : "No namespace sandbox is installed; Docker/Podman requires a digest-pinned image." } : {}
  });
}
var sandboxUnavailableReasons = /* @__PURE__ */ new Map();
var sandboxBackendFailures = /* @__PURE__ */ new Set();
var sandboxEnvironmentKey = (env) => JSON.stringify({
  path: env?.PATH || process.env.PATH || "",
  backend: env?.DEEPSCIENTIST_MATH_SANDBOX_BACKEND || "",
  image: env?.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || "",
  sealedEnvironment: env?.DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT || ""
});
var sandboxBackendKey = (environmentKey, backend) => `${environmentKey}\0${backend}`;
var resolveSandboxBackends = (env, capability = inspectMathematicsSandboxBackends(env || process.env)) => {
  const environmentKey = sandboxEnvironmentKey(env);
  return capability.available.filter((kind) => !sandboxBackendFailures.has(sandboxBackendKey(environmentKey, kind))).toSorted((left, right) => {
    if (left === capability.preferred) return -1;
    if (right === capability.preferred) return 1;
    return 0;
  }).map(
    (kind) => Object.freeze({
      kind,
      executable: executableOnPath(kind, env?.PATH) || `/usr/bin/${kind}`
    })
  );
};
var isSandboxBackendFailure = (backend, result2) => result2.errorCode === "EPERM" || /(?:uid_map|gid_map|unshare:.*(?:operation not permitted|permission denied)|bwrap:.*(?:operation not permitted|permission denied)|(?:namespace|clone|loopback).*(?:operation not permitted|permission denied))/iu.test(
  `${result2.stderr}
${result2.stdout}`
) || (backend === "docker" || backend === "podman") && (result2.exitCode === 125 || result2.errorCode === "EACCES" || result2.errorCode === "ENOENT");
var bwrapProjectPath = (projectRelative) => projectRelative ? `/workspace/${projectRelative}` : "/workspace";
var sandboxVariables = (input, omitEmptyTestHooks = false) => [
  ["PATH", `${input.runtimeRoot ? "/runtime/node:/runtime/node/bin:" : ""}${input.toolchainBin ? `${input.toolchainBin}:` : ""}/usr/local/bin:/usr/bin:/bin`],
  ["HOME", "/tmp"],
  ["TMPDIR", "/tmp"],
  ["LANG", "C.UTF-8"],
  ["ELAN_HOME", "/toolchains/elan"],
  ["LEAN_NUM_THREADS", "1"],
  ["LEAN_STACK_SIZE_KB", "8192"],
  ...[["DEEPSCIENTIST_TEST_LEAN_COUNTER", input.testCounter], ["DEEPSCIENTIST_TEST_LEAN_AXIOMS", input.testAxioms]].filter(([, value]) => value || !omitEmptyTestHooks)
];
var buildBwrapArguments = (input) => {
  const projectPath = bwrapProjectPath(input.projectRelative);
  const packagesPath = input.lakePackagesMountPath ?? `${projectPath}/.lake/packages`;
  if (input.lakePackagesPath && !input.lakePackagesMountPath) {
    import_node_fs8.default.mkdirSync(import_node_path9.default.join(input.candidateRoot, input.projectRelative, ".lake", "packages"), { recursive: true });
  }
  const args = [
    "--unshare-user",
    "--uid",
    "0",
    "--gid",
    "0",
    "--unshare-net",
    "--unshare-pid",
    "--die-with-parent",
    "--new-session",
    "--clearenv",
    "--ro-bind",
    "/usr",
    "/usr",
    "--symlink",
    "usr/bin",
    "/bin",
    "--symlink",
    "usr/sbin",
    "/sbin",
    "--symlink",
    "usr/lib",
    "/lib",
    "--symlink",
    "usr/lib64",
    "/lib64",
    "--bind",
    input.candidateRoot,
    "/workspace",
    "--tmpfs",
    "/tmp",
    "--proc",
    "/proc",
    "--dev",
    "/dev",
    "--dir",
    "/toolchains",
    "--dir",
    "/runtime"
  ];
  if (input.lakePackagesFd !== void 0) args.push("--ro-bind-fd", String(input.lakePackagesFd), packagesPath);
  else if (input.lakePackagesPath)
    args.push(input.writablePackageOverlay ? "--bind" : "--ro-bind", input.lakePackagesPath, packagesPath);
  if (input.lakePackageOverridesPath)
    args.push("--ro-bind", input.lakePackageOverridesPath, `${projectPath}/.lake/package-overrides.json`);
  if (input.toolchainRoot) args.push("--ro-bind", input.toolchainRoot, "/toolchains/elan");
  if (input.leanLauncherPath && input.toolchainBin) {
    const relativeBin = import_node_path9.default.relative("/toolchains/elan", input.toolchainBin);
    args.push("--ro-bind", import_node_path9.default.dirname(import_node_path9.default.join(input.toolchainRoot, relativeBin)), "/runtime/pinned-lean");
    args.push("--ro-bind", input.leanLauncherPath, `${input.toolchainBin}/lean`);
  }
  if (input.runtimeRoot) args.push("--ro-bind", input.runtimeRoot, "/runtime/node");
  args.push(
    "--chdir",
    projectPath,
    ...sandboxVariables(input).flatMap(([name, value]) => ["--setenv", name, value]),
    "--",
    "/bin/sh",
    "-ceu",
    `ulimit -v ${LEAN_SANDBOX_ADDRESS_SPACE_KB} 2>/dev/null || true; ulimit -u ${LEAN_SANDBOX_PROCESS_LIMIT} 2>/dev/null || true; ulimit -n 4096 2>/dev/null || true; exec "$@"`,
    "--",
    input.command,
    ...input.commandArgs
  );
  return args;
};
var buildContainerArguments = (input) => {
  const projectPath = bwrapProjectPath(input.projectRelative);
  return [
    "run",
    "--rm",
    ...input.interactive ? ["--interactive"] : [],
    ...input.cidfile ? ["--cidfile", input.cidfile] : [],
    "--network=none",
    "--pull=never",
    "--read-only",
    "--pids-limit=256",
    "--memory=8g",
    "--cpus=4",
    "--ulimit",
    "nofile=4096:4096",
    "--ulimit",
    "fsize=67108864:67108864",
    "--cap-drop=ALL",
    "--security-opt=no-new-privileges",
    "--user",
    `${process.getuid?.() ?? 0}:${process.getgid?.() ?? 0}`,
    "--tmpfs",
    "/tmp:rw,nosuid,nodev,mode=1777",
    "--tmpfs",
    "/etc:ro,nosuid,nodev,noexec,mode=755",
    "--mount",
    `type=bind,src=${input.checkoutRoot},dst=/workspace`,
    ...input.toolchainRoot ? ["--mount", `type=bind,src=${input.toolchainRoot},dst=/toolchains/elan,ro`] : [],
    ...input.runtimeRoot ? ["--mount", `type=bind,src=${input.runtimeRoot},dst=/runtime/node,ro`] : [],
    ...input.lakePackagesPath ? ["--mount", `type=bind,src=${input.lakePackagesPath},dst=${projectPath}/.lake/packages,ro`] : [],
    ...input.lakePackageOverridesPath ? ["--mount", `type=bind,src=${input.lakePackageOverridesPath},dst=${projectPath}/.lake/package-overrides.json,ro`] : [],
    "--workdir",
    projectPath,
    ...sandboxVariables(input, true).flatMap(([name, value]) => ["--env", `${name}=${value}`]),
    input.image,
    input.command,
    ...input.commandArgs
  ];
};
var createMathematicsSandboxRoot = (temporaryRoot) => {
  const sandboxRoot = import_node_path9.default.join(temporaryRoot, "sandbox");
  for (const directory of ["usr", "workspace", "tmp", "proc", "dev", "toolchains/elan"]) {
    import_node_fs8.default.mkdirSync(import_node_path9.default.join(sandboxRoot, directory), { recursive: true });
  }
  for (const [link, target] of [
    ["bin", "usr/bin"],
    ["sbin", "usr/sbin"],
    ["lib", "usr/lib"],
    ["lib64", "usr/lib64"]
  ]) {
    import_node_fs8.default.symlinkSync(target, import_node_path9.default.join(sandboxRoot, link));
  }
  return sandboxRoot;
};
var runLeanSandboxed = async (input) => {
  const leaseStartedAt = Date.now();
  let proofLease;
  try {
    proofLease = await acquireMathProofEnvironmentLease(
      import_node_path9.default.join(input.checkoutRoot, input.projectRelative),
      input.env ?? process.env,
      input.signal,
      leaseStartedAt + input.timeoutMs
    );
  } catch (error) {
    if (input.signal?.aborted || error instanceof Error && error.name === "AbortError")
      return { ...unavailableProcessResult("Lean environment lease was cancelled."), aborted: true };
    if (error instanceof Error && error.name === "TimeoutError")
      return { ...unavailableProcessResult("Lean environment lease exceeded the operation deadline."), timedOut: true };
    throw error;
  }
  let sealedRootFd;
  let temporaryRoot;
  let stagedCommandPath;
  try {
    if (proofLease) {
      input = { ...input, timeoutMs: input.timeoutMs - (Date.now() - leaseStartedAt) };
      if (input.timeoutMs <= 0)
        return {
          ...unavailableProcessResult("Lean environment lease exceeded the operation deadline."),
          timedOut: true
        };
    }
    if (proofLease && input.lakePackagesPath !== proofLease.packagesRoot)
      return unavailableProcessResult("Lean sandbox sealed package binding mismatch.");
    if (input.lakePackagesPath && !input.lakePackagesMountPath && import_node_fs8.default.lstatSync(import_node_path9.default.join(input.checkoutRoot, input.projectRelative, ".lake", "packages"), {
      throwIfNoEntry: false
    })?.isSymbolicLink()) {
      try {
        const mountPath = ensureLakePackagesMountPoint(
          import_node_path9.default.join(input.checkoutRoot, input.projectRelative),
          input.checkoutRoot
        );
        if (mountPath) input = { ...input, lakePackagesMountPath: mountPath };
      } catch (error) {
        return unavailableProcessResult(error instanceof Error ? error.message : String(error));
      }
    }
    const environmentKey = sandboxEnvironmentKey(input.env);
    const capability = input.sandboxCapability ?? inspectMathematicsSandboxBackends(input.env || process.env);
    const unavailableReason = sandboxUnavailableReasons.get(environmentKey);
    if (unavailableReason) return unavailableProcessResult(unavailableReason);
    const backends = resolveSandboxBackends(input.env, capability).filter(
      (backend) => !proofLease && !input.lakePackagesMountPath || backend.kind === "bwrap"
    );
    if (backends.length === 0) {
      if (proofLease)
        return unavailableProcessResult("Sealed proof environments require the bwrap file-descriptor mount backend.");
      const reason = capability.available.length ? "Lean verification capability unavailable: this host does not permit the required Linux namespace or container sandbox." : "Lean verification capability unavailable: this host has no supported Linux sandbox backend (unshare, bwrap, Docker, or Podman).";
      if (capability.available.length === 0) sandboxUnavailableReasons.set(environmentKey, reason);
      return unavailableProcessResult(reason);
    }
    if (proofLease) {
      const before = import_node_fs8.default.statSync(proofLease.packagesRoot, { bigint: true });
      sealedRootFd = import_node_fs8.default.openSync(proofLease.packagesRoot, import_node_fs8.default.constants.O_RDONLY | import_node_fs8.default.constants.O_DIRECTORY);
      const opened = import_node_fs8.default.fstatSync(sealedRootFd, { bigint: true });
      resolveMathProofEnvironment(
        import_node_path9.default.join(input.checkoutRoot, input.projectRelative),
        input.env ?? process.env
      ).verify();
      if (!opened.isDirectory() || opened.dev !== before.dev || opened.ino !== before.ino)
        return unavailableProcessResult("Sealed proof environment descriptor changed before sandbox execution.");
    }
    const sandboxCommand = import_node_path9.default.basename(input.command);
    const pathEntries = (input.env?.PATH || process.env.PATH || "").split(import_node_path9.default.delimiter).filter(Boolean);
    const resolvedCommand = import_node_path9.default.isAbsolute(input.command) ? input.command : pathEntries.map((entry) => import_node_path9.default.join(entry, input.command)).find((candidate) => import_node_fs8.default.existsSync(candidate));
    const trustedElanHome = resolveTrustedElanHome(input.env);
    const trustedToolchainBin = resolveTrustedToolchainBin(
      input.checkoutRoot,
      input.projectRelative,
      input.env,
      trustedElanHome
    );
    const mountedElanHome = trustedToolchainBin ? import_node_path9.default.dirname(trustedToolchainBin) : trustedElanHome;
    const mountedToolchainBin = trustedToolchainBin ? "/toolchains/elan/bin" : "";
    const trustedCommandRoot = (candidate) => {
      try {
        const canonical = import_node_fs8.default.realpathSync(candidate);
        return Boolean(
          trustedElanHome && canonical === import_node_path9.default.join(trustedElanHome, "bin", sandboxCommand) || trustedToolchainBin && canonical === import_node_path9.default.join(trustedToolchainBin, sandboxCommand)
        );
      } catch {
        return false;
      }
    };
    const customSourceCommand = resolvedCommand && import_node_fs8.default.existsSync(resolvedCommand) && !trustedCommandRoot(import_node_path9.default.resolve(resolvedCommand)) && !OFFICIAL_EXECUTABLE_ALLOWLIST.has(sandboxCommand) ? resolvedCommand : void 0;
    const customCommand = Boolean(customSourceCommand);
    temporaryRoot = import_node_fs8.default.mkdtempSync(import_node_path9.default.join(import_node_os3.default.tmpdir(), "deepscientist-lean-sandbox-"));
    const sandboxRoot = createMathematicsSandboxRoot(temporaryRoot);
    let leanLauncherPath;
    if (trustedToolchainBin && mountedToolchainBin) {
      leanLauncherPath = import_node_path9.default.join(temporaryRoot, "lean-launcher");
      const prefix = `'${import_node_path9.default.dirname(mountedToolchainBin).replaceAll("'", "'\\''")}'`;
      import_node_fs8.default.writeFileSync(
        leanLauncherPath,
        `#!/bin/sh
if [ "$#" = 1 ] && [ "$1" = --print-prefix ]; then printf '%s\\n' ${prefix}; exit 0; fi
exec /runtime/pinned-lean/bin/lean "$@" -j1
`,
        { mode: 365 }
      );
      import_node_fs8.default.chmodSync(leanLauncherPath, 365);
    }
    const sessionContainerIdFile = input.onDuplexSpawn ? import_node_path9.default.join(temporaryRoot, "session.cid") : void 0;
    let sessionContainerExecutable;
    const projectOverridesPath = import_node_path9.default.join(
      input.checkoutRoot,
      input.projectRelative,
      ".lake",
      "package-overrides.json"
    );
    let sandboxPackageOverridesPath;
    if (input.lakePackagesPath && (proofLease || import_node_fs8.default.existsSync(projectOverridesPath))) {
      if (proofLease && !import_node_fs8.default.existsSync(projectOverridesPath)) {
        import_node_fs8.default.mkdirSync(import_node_path9.default.dirname(projectOverridesPath), { recursive: true, mode: 448 });
        import_node_fs8.default.writeFileSync(projectOverridesPath, `${JSON.stringify({ schemaVersion: "1.2.0", packages: [] })}
`, {
          flag: "wx",
          mode: 384
        });
      }
      sandboxPackageOverridesPath = import_node_path9.default.join(temporaryRoot, "package-overrides.json");
      const manifest = JSON.parse(
        import_node_fs8.default.readFileSync(import_node_path9.default.join(input.checkoutRoot, input.projectRelative, "lake-manifest.json"), "utf8")
      );
      const packages = manifest.packages.map((entry) => {
        const name = typeof entry.name === "string" ? entry.name : "";
        if (!name || /[/\\]/u.test(name) || name.includes("\0") || name === "." || name === "..")
          throw new Error("Sealed environment contains an invalid package name.");
        const directory = [name, name.replace(/^«(.+)»$/u, "$1")].find(
          (candidate) => import_node_fs8.default.statSync(import_node_path9.default.join(input.lakePackagesPath, candidate), { throwIfNoEntry: false })?.isDirectory()
        );
        if (!directory) throw new Error("Sealed environment package is absent.");
        return {
          ...entry,
          type: "path",
          dir: import_node_path9.default.posix.join(
            input.lakePackagesMountPath ?? import_node_path9.default.posix.join("/workspace", input.projectRelative, ".lake/packages"),
            directory
          )
        };
      });
      import_node_fs8.default.writeFileSync(sandboxPackageOverridesPath, JSON.stringify({ schemaVersion: "1.2.0", packages }) + "\n", {
        mode: 384
      });
    }
    let commandForSandbox = sandboxCommand;
    if (customCommand) {
      const customName = `deepscientist-verifier-${import_node_crypto4.default.randomUUID()}`;
      const customPath = import_node_path9.default.join(input.checkoutRoot, `.${customName}`);
      stagedCommandPath = customPath;
      try {
        import_node_fs8.default.copyFileSync(customSourceCommand, customPath);
        import_node_fs8.default.chmodSync(customPath, 493);
      } catch {
        return unavailableProcessResult(
          `Lean verifier executable could not be staged: ${customSourceCommand || input.command}`
        );
      }
      commandForSandbox = `/workspace/.${customName}`;
    } else if (!OFFICIAL_EXECUTABLE_ALLOWLIST.has(sandboxCommand)) {
      return unavailableProcessResult(`Lean verifier executable is not allowed in the sandbox: ${sandboxCommand}`);
    }
    const testCounterPath = input.env?.DEEPSCIENTIST_TEST_LEAN_COUNTER;
    const sandboxEnv = officialComparatorEnvironment(input.env);
    const sandboxCounterPath = import_node_path9.default.join(input.checkoutRoot, ".deepscientist-test-counter");
    if (testCounterPath) sandboxEnv.DEEPSCIENTIST_TEST_LEAN_COUNTER = "/workspace/.deepscientist-test-counter";
    const nodeExecutable = pathEntries.map((entry) => import_node_path9.default.join(entry, "node")).find((candidate) => import_node_fs8.default.existsSync(candidate));
    const runtimeRoot = import_node_path9.default.resolve(import_node_path9.default.dirname(nodeExecutable || process.execPath), "..");
    const configuredRuntimeRoot = input.env?.DEEPSCIENTIST_MATH_TRUSTED_RUNTIME_ROOT || process.env.DEEPSCIENTIST_MATH_TRUSTED_RUNTIME_ROOT;
    const configuredToolsRoot = input.env?.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT;
    let trustedRuntimeRoot = "";
    if (customCommand || configuredToolsRoot) {
      try {
        const canonicalRuntime = import_node_fs8.default.realpathSync(customCommand ? configuredRuntimeRoot || runtimeRoot : configuredToolsRoot);
        if (import_node_fs8.default.statSync(canonicalRuntime).isDirectory()) trustedRuntimeRoot = canonicalRuntime;
      } catch {
        trustedRuntimeRoot = "";
      }
    }
    try {
      const mounts = {
        projectRelative: input.projectRelative.replaceAll(import_node_path9.default.sep, "/"),
        toolchainRoot: mountedElanHome,
        toolchainBin: mountedToolchainBin,
        runtimeRoot: trustedRuntimeRoot,
        lakePackagesPath: input.lakePackagesPath || "",
        lakePackageOverridesPath: sandboxPackageOverridesPath,
        command: commandForSandbox,
        commandArgs: input.args,
        testCounter: testCounterPath ? "/workspace/.deepscientist-test-counter" : "",
        testAxioms: input.env?.DEEPSCIENTIST_TEST_LEAN_AXIOMS || ""
      };
      const runBackend = (backend) => {
        const args = backend.kind === "unshare" ? [
          "--user",
          "--map-root-user",
          "--net",
          "--mount",
          "--pid",
          "--fork",
          "--kill-child=SIGKILL",
          "/bin/sh",
          "-ceu",
          LEAN_SANDBOX_SCRIPT,
          "--",
          sandboxRoot,
          input.checkoutRoot,
          mounts.projectRelative,
          mountedElanHome,
          mountedToolchainBin,
          trustedRuntimeRoot,
          "/workspace/.deepscientist-test-counter",
          mounts.testAxioms,
          input.lakePackagesPath || "",
          sandboxPackageOverridesPath || "",
          commandForSandbox,
          ...input.args
        ] : backend.kind === "bwrap" ? buildBwrapArguments({
          ...mounts,
          candidateRoot: input.checkoutRoot,
          lakePackagesMountPath: input.lakePackagesMountPath,
          lakePackagesFd: sealedRootFd === void 0 ? void 0 : 3,
          // The shell launcher is only reliable inside the sealed proof
          // image; the unsealed official `lake test` build cannot exec a
          // bind-mounted script for its final Challenge job. The real
          // pinned toolchain binary is used there instead.
          leanLauncherPath: sealedRootFd === void 0 ? void 0 : leanLauncherPath
        }) : buildContainerArguments({
          ...mounts,
          checkoutRoot: input.checkoutRoot,
          interactive: Boolean(input.onDuplexSpawn || input.stdin !== void 0),
          cidfile: sessionContainerIdFile,
          image: input.env?.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || process.env.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || ""
        });
        return runLeanProcess(backend.executable, args, {
          cwd: import_node_path9.default.join(input.checkoutRoot, input.projectRelative),
          timeoutMs: input.timeoutMs,
          signal: input.signal,
          env: { ...sandboxEnv, DEEPSCIENTIST_MATH_LEAN_LOCK: input.env?.DEEPSCIENTIST_MATH_LEAN_LOCK },
          stdin: input.stdin,
          outputCapture: input.outputCapture,
          outputLimit: input.outputLimit,
          onDuplexSpawn: input.onDuplexSpawn,
          ...backend.kind === "bwrap" && sealedRootFd !== void 0 ? { inheritedFds: [sealedRootFd] } : {}
        });
      };
      let result2;
      for (const backend of backends) {
        if (sessionContainerIdFile && (backend.kind === "docker" || backend.kind === "podman"))
          sessionContainerExecutable = backend.executable;
        result2 = Object.freeze({ ...await runBackend(backend), sandboxBackend: backend.kind });
        if (!isSandboxBackendFailure(backend.kind, result2)) break;
        sandboxBackendFailures.add(sandboxBackendKey(environmentKey, backend.kind));
        if (input.onDuplexSpawn) break;
      }
      if (isSandboxBackendFailure(result2.sandboxBackend || backends[backends.length - 1].kind, result2)) {
        const reason = "Lean verification capability unavailable: this host does not permit the required Linux namespace or container sandbox.";
        sandboxUnavailableReasons.set(environmentKey, reason);
        return unavailableProcessResult(reason);
      }
      if (testCounterPath?.startsWith("/") && import_node_fs8.default.existsSync(sandboxCounterPath)) {
        import_node_fs8.default.copyFileSync(sandboxCounterPath, testCounterPath);
        import_node_fs8.default.rmSync(sandboxCounterPath, { force: true });
      }
      return result2;
    } finally {
      if (sessionContainerExecutable && sessionContainerIdFile && import_node_fs8.default.existsSync(sessionContainerIdFile)) {
        const containerId = import_node_fs8.default.readFileSync(sessionContainerIdFile, "utf8").trim();
        if (/^[a-f0-9]{12,64}$/u.test(containerId)) {
          await runMathProcess(sessionContainerExecutable, ["rm", "--force", containerId], {
            cwd: input.checkoutRoot,
            timeoutMs: 5e3,
            env: sandboxEnv
          });
        }
      }
    }
  } finally {
    try {
      if (stagedCommandPath) import_node_fs8.default.rmSync(stagedCommandPath, { force: true });
      if (temporaryRoot) import_node_fs8.default.rmSync(temporaryRoot, { recursive: true, force: true });
    } finally {
      if (sealedRootFd !== void 0) import_node_fs8.default.closeSync(sealedRootFd);
      await proofLease?.release();
    }
  }
};
async function runMathematicsSandboxedCommand(input) {
  const runtimeEnv = resolveMathematicsRuntimeEnvironment(input.env || process.env);
  if (input.stdin !== void 0) {
    if (typeof input.stdin !== "string") {
      return unavailableProcessResult("Lean sandbox stdin must be a string.");
    }
    if (input.stdin.includes("\0")) {
      return unavailableProcessResult("Lean sandbox stdin must not contain NUL bytes.");
    }
    if (Buffer.byteLength(input.stdin, "utf8") > MAX_SANDBOX_STDIN_BYTES) {
      return unavailableProcessResult(`Lean sandbox stdin exceeds the ${MAX_SANDBOX_STDIN_BYTES}-byte limit.`);
    }
  }
  const checkoutRoot = import_node_path9.default.resolve(input.checkoutRoot);
  const requested = (input.projectRelative ?? "").trim(), projectRelative = requested && repositoryRelativePath(requested, true);
  if (projectRelative === void 0) return unavailableProcessResult("Lean sandbox project path must be repository-relative.");
  const projectRoot = import_node_path9.default.join(checkoutRoot, projectRelative);
  try {
    const rootStat = import_node_fs8.default.lstatSync(checkoutRoot);
    const projectStat = import_node_fs8.default.lstatSync(projectRoot);
    if (rootStat.isSymbolicLink() || !rootStat.isDirectory() || projectStat.isSymbolicLink() || !projectStat.isDirectory()) {
      return unavailableProcessResult("Lean sandbox checkout and project must be regular directories.");
    }
    assertNoSymlinkTraversal(checkoutRoot, projectRoot, "Lean sandbox project");
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return unavailableProcessResult(
      message.includes("symlink") ? message : "Lean sandbox checkout or project directory is missing."
    );
  }
  const sealed = resolveMathProofEnvironment(projectRoot, runtimeEnv);
  let lakePackagesPath;
  if (input.useWorkspacePackagesOnly && input.lakePackagesPath) {
    return unavailableProcessResult("Private workspace packages cannot be combined with an external package mount.");
  }
  if (sealed) {
    if (input.useWorkspacePackagesOnly || input.lakePackagesPath && input.lakePackagesPath !== sealed.packagesRoot)
      return unavailableProcessResult("Lean sandbox sealed package binding mismatch.");
    lakePackagesPath = sealed.packagesRoot;
  } else if (input.lakePackagesPath) {
    try {
      const packageStat = import_node_fs8.default.lstatSync(input.lakePackagesPath);
      if (packageStat.isSymbolicLink() || !packageStat.isDirectory()) {
        return unavailableProcessResult("Lean sandbox Lake package cache must be a regular directory.");
      }
      lakePackagesPath = import_node_fs8.default.realpathSync(input.lakePackagesPath);
    } catch {
      return unavailableProcessResult("Lean sandbox Lake package cache is missing.");
    }
  } else if (!input.useWorkspacePackagesOnly) {
    lakePackagesPath = resolveMathematicsLakePackagesCache(projectRoot, runtimeEnv);
  }
  let lakePackagesMountPath;
  if (lakePackagesPath) {
    try {
      lakePackagesMountPath = ensureLakePackagesMountPoint(projectRoot, checkoutRoot);
    } catch (error) {
      return unavailableProcessResult(error instanceof Error ? error.message : String(error));
    }
  }
  return runLeanSandboxed({
    ...lakePackagesMountPath ? { lakePackagesMountPath } : {},
    checkoutRoot,
    projectRelative,
    command: input.command,
    args: [...input.args ?? []],
    ...input.stdin !== void 0 ? { stdin: input.stdin } : {},
    timeoutMs: input.timeoutMs,
    signal: input.signal,
    env: runtimeEnv,
    lakePackagesPath,
    outputCapture: input.outputCapture,
    outputLimit: input.outputLimit,
    onDuplexSpawn: input.onDuplexSpawn
  });
}

// src/math/leanToolchainReadiness.ts
var import_node_fs9 = __toESM(require("node:fs"));
var import_node_path10 = __toESM(require("node:path"));
var import_node_child_process3 = require("node:child_process");
var MAX_DIAGNOSTICS = 2e3;
var DEFAULT_TIMEOUT_MS2 = 1e4;
var bounded = (value) => limitMathOutput(value.trim().replace(/\s+/gu, " "), MAX_DIAGNOSTICS, "head");
var fingerprint = (value) => mathDigest(
  JSON.stringify({
    schema: "deepscientist.mathematics.lean-toolchain-readiness.v1",
    ...value
  })
);
var result = (value) => Object.freeze({ ...value, fingerprint: fingerprint(value) });
function executableInPath(name, env) {
  const candidates = name.includes(import_node_path10.default.sep) ? [name] : (env.PATH || "").split(import_node_path10.default.delimiter).filter(Boolean).map((entry) => import_node_path10.default.join(entry, name));
  for (const candidate of candidates) {
    try {
      const stat = import_node_fs9.default.statSync(candidate);
      if (stat.isFile() && (process.platform === "win32" || (stat.mode & 73) !== 0)) {
        return import_node_path10.default.resolve(candidate);
      }
    } catch {
    }
  }
  return void 0;
}
function readToolchain(projectRoot) {
  const file = import_node_path10.default.join(projectRoot, "lean-toolchain");
  const stat = import_node_fs9.default.lstatSync(file);
  if (stat.isSymbolicLink() || !stat.isFile()) {
    throw new Error("lean-toolchain must be a regular file");
  }
  const source = import_node_fs9.default.readFileSync(file, "utf8");
  const lines = source.split(/\r?\n/u).map((line) => line.trim()).filter(Boolean);
  if (lines.length !== 1 || lines[0].length > 256 || ["\0", "\r", "\n"].some((value) => lines[0].includes(value))) {
    throw new Error("lean-toolchain must contain exactly one non-empty toolchain identifier");
  }
  return lines[0];
}
function checkResolvedLeanToolchainReadiness(request) {
  const requestedRoot = typeof request.projectRoot === "string" ? request.projectRoot.trim() : "";
  const projectRoot = requestedRoot ? import_node_path10.default.resolve(requestedRoot) : "";
  const base = { projectRoot };
  if (!projectRoot) {
    return result({ ...base, status: "invalid", diagnostics: "Lean project root is required" });
  }
  let stat;
  try {
    stat = import_node_fs9.default.lstatSync(projectRoot);
  } catch (error) {
    return result({
      ...base,
      status: "invalid",
      diagnostics: `Lean project root is unavailable: ${bounded(error instanceof Error ? error.message : String(error))}`
    });
  }
  if (!stat.isDirectory() || stat.isSymbolicLink()) {
    return result({ ...base, status: "invalid", diagnostics: "Lean project root must be a regular directory" });
  }
  const env = request.env;
  let toolchain;
  try {
    toolchain = readToolchain(projectRoot);
  } catch (error) {
    return result({
      ...base,
      status: "invalid",
      diagnostics: bounded(error instanceof Error ? error.message : String(error))
    });
  }
  const lakePath = executableInPath("lake", env);
  const leanPath = executableInPath("lean", env);
  if (!lakePath || !leanPath) {
    return result({
      ...base,
      status: "unavailable",
      ...lakePath ? { lakePath } : {},
      ...leanPath ? { leanPath } : {},
      toolchain,
      diagnostics: `Pinned Lean tools are unavailable (lake=${lakePath ? "found" : "missing"}, lean=${leanPath ? "found" : "missing"})`
    });
  }
  const timeoutMs = Math.max(250, Math.min(18e4, request.timeoutMs ?? DEFAULT_TIMEOUT_MS2));
  let probe;
  try {
    probe = (0, import_node_child_process3.spawnSync)(leanPath, ["--version"], {
      cwd: projectRoot,
      env,
      encoding: "utf8",
      timeout: timeoutMs,
      maxBuffer: 32 * 1024
    });
  } catch (error) {
    return result({
      ...base,
      status: "unavailable",
      lakePath,
      leanPath,
      toolchain,
      diagnostics: `Lean toolchain probe could not start: ${bounded(error instanceof Error ? error.message : String(error))}`
    });
  }
  const output = bounded(`${probe.stdout || ""} ${probe.stderr || ""}`);
  if (probe.error || probe.status !== 0) {
    const suffix = probe.signal === "SIGTERM" ? ` (timed out after ${timeoutMs}ms)` : "";
    return result({
      ...base,
      status: "unavailable",
      lakePath,
      leanPath,
      toolchain,
      diagnostics: `Lean toolchain probe failed${suffix}${output ? `: ${output}` : ""}`
    });
  }
  const expectedVersion = /^(?:leanprover\/lean4:)?v?(\d+\.\d+\.\d+(?:-rc\d+)?)$/u.exec(toolchain)?.[1];
  const actualVersion = /\bLean \(version ([^\s,)]+)/u.exec(probe.stdout?.toString() || "")?.[1];
  if (expectedVersion && actualVersion !== expectedVersion) return result({
    ...base,
    status: "invalid",
    lakePath,
    leanPath,
    toolchain,
    diagnostics: `Pinned Lean version mismatch: expected ${expectedVersion}, found ${actualVersion ?? "unrecognized version output"}. Check PATH and ELAN_HOME.`
  });
  return result({
    ...base,
    status: "ready",
    lakePath,
    leanPath,
    toolchain,
    diagnostics: output || "lean --version succeeded"
  });
}

// src/math/leanDiagnosticMessages.ts
var position = (value) => typeof value === "number" && Number.isSafeInteger(value) && value >= 0;
var goalText = (message) => /(?:^|\n)unsolved goals\n([\s\S]+)/u.exec(message)?.[1];
function rawMessages(output) {
  return output.split(/(?=^.+:\d+:\d+:\s*(?:error|warning|info)(?:\([^\n)]*\))?:)/mu).flatMap((block) => {
    const header = /^(.+):(\d+):(\d+):\s*(error|warning|info)(?:\(([^\n)]*)\))?:\s*([\s\S]*)/u.exec(block);
    if (!header) return [];
    const message = header[6].trimEnd();
    return [{
      format: "raw",
      file: header[1],
      line: Number(header[2]),
      column: Math.max(0, Number(header[3]) - 1),
      severity: header[4],
      message,
      ...header[5] ? { code: header[5] } : {},
      ...goalText(message) ? { goalText: goalText(message) } : {}
    }];
  });
}
function parseLeanDiagnosticOutput(output) {
  const messages = [], raw = [];
  let pending = [];
  const flush = () => {
    messages.push(...rawMessages(pending.join("\n")));
    pending = [];
  };
  for (const line of output.split("\n")) {
    if (!line.trim()) {
      raw.push(line);
      pending.push(line);
      continue;
    }
    let value;
    try {
      value = JSON.parse(line);
    } catch {
    }
    if (value && typeof value === "object" && !Array.isArray(value) && typeof value.data === "string" && ["error", "warning", "info"].includes(value.severity)) {
      flush();
      messages.push({
        format: "lean-json",
        severity: value.severity,
        message: value.data,
        ...typeof value.fileName === "string" ? { file: value.fileName } : {},
        ...position(value.pos?.line) && position(value.pos?.column) ? { line: value.pos.line, column: value.pos.column } : {},
        ...position(value.endPos?.line) && position(value.endPos?.column) ? { endLine: value.endPos.line, endColumn: value.endPos.column } : {},
        ...typeof value.kind === "string" && value.kind !== "[anonymous]" ? { code: value.kind } : {},
        ...goalText(value.data) ? { goalText: goalText(value.data) } : {}
      });
    } else {
      raw.push(line);
      pending.push(line);
    }
  }
  flush();
  const fallback = raw.join("\n");
  return { messages, raw: fallback };
}
function renderLeanDiagnosticMessage(message) {
  const location = message.file ? `${message.file}${message.line === void 0 ? "" : `:${message.line}:${(message.column ?? 0) + 1}`}: ` : "";
  return `${location}${message.severity}${message.code ? `(${message.code})` : ""}: ${message.message}`;
}
function renderLeanDiagnosticOutput(output) {
  const parsed = parseLeanDiagnosticOutput(output);
  const json = parsed.messages.filter((message) => message.format === "lean-json").map(renderLeanDiagnosticMessage).join("\n");
  return [json, parsed.raw].filter(Boolean).join("\n");
}

// src/math/leanResidualGoals.ts
var digest2 = external_exports.string().regex(/^[a-f0-9]{64}$/u);
var diagnosticExit = external_exports.union([external_exports.literal(0), external_exports.literal(1)]);
var sourceFile = external_exports.object({ file: external_exports.string(), digest: digest2 });
var reference = external_exports.object({
  path: external_exports.string(),
  digest: digest2,
  sourceDigest: digest2,
  environmentDigest: digest2,
  captureComplete: external_exports.boolean().nullable()
});
var latestSchema = external_exports.object({
  schema: external_exports.literal("theoremos.lean-diagnostics-latest.v1"),
  authority: external_exports.literal("advisory-lean-process"),
  sourceDigest: digest2,
  environmentDigest: digest2,
  toolIdentity: digest2,
  requestedFiles: external_exports.array(external_exports.string()).min(1).max(4096),
  configuration: external_exports.array(external_exports.object({ file: external_exports.string(), digest: digest2.nullable() })).length(LAKE_CONFIGURATION_FILES.length),
  sourceFiles: external_exports.array(sourceFile).min(1).max(4096),
  exitCode: diagnosticExit,
  timedOut: external_exports.literal(false),
  aborted: external_exports.literal(false),
  diagnosticArtifacts: external_exports.array(reference).max(4096)
});
var artifactSchema = external_exports.object({
  schema: external_exports.literal("theoremos.lean-diagnostics.v1"),
  authority: external_exports.literal("advisory-lean-process"),
  sourceDigest: digest2,
  environmentDigest: digest2,
  toolIdentity: digest2,
  file: external_exports.string(),
  sourceCurrent: external_exports.literal(true),
  sourceFiles: external_exports.array(sourceFile).min(1).max(4096),
  exitCode: diagnosticExit,
  timedOut: external_exports.literal(false),
  aborted: external_exports.literal(false),
  captureComplete: external_exports.literal(true),
  stdout: external_exports.string(),
  stderr: external_exports.string(),
  stdoutSha256: digest2,
  stderrSha256: digest2
});
function leanDiagnosticEnvironmentIdentity(projectRoot, source) {
  const env = resolveMathematicsRuntimeEnvironment(source);
  const sealed = resolveMathProofEnvironment(projectRoot, env);
  const toolIdentity = formalVerificationToolIdentity(projectRoot, env);
  return { environmentDigest: mathDigest(JSON.stringify([
    "lean-json-diagnostics.v1",
    sealed?.identity,
    env.PATH,
    env.ELAN_HOME,
    env.LEAN_PATH,
    env.LEAN_SYSROOT,
    toolIdentity
  ])), ...toolIdentity ? { toolIdentity } : {} };
}

// src/math/leanDiagnostics.ts
var DIAGNOSTIC_CAPTURE_LIMIT = 4e6;
async function runWorkerLean(project, module2, output, env, timeoutMs, signal, outputLimit) {
  const startedAt = Date.now(), deadlineAt = startedAt + timeoutMs;
  const stopped = () => ({
    started: false,
    exitCode: null,
    timedOut: !signal?.aborted,
    aborted: Boolean(signal?.aborted),
    durationMs: Date.now() - startedAt,
    stdout: "",
    stderr: ""
  });
  let lease;
  try {
    lease = await acquireMathProofEnvironmentLease(project, env, signal, deadlineAt);
  } catch (error) {
    if (signal?.aborted || error instanceof Error && error.name === "TimeoutError") return stopped();
    throw error;
  }
  if (!lease) throw new Error("math_diagnostics_worker_environment_missing");
  try {
    if (signal?.aborted || Date.now() >= deadlineAt) return stopped();
    const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env, timeoutMs: Math.min(1e4, deadlineAt - Date.now()) });
    if (signal?.aborted || Date.now() >= deadlineAt) return stopped();
    if (readiness.status !== "ready" || !readiness.leanPath) throw new Error("math_diagnostics_lean_unavailable");
    const libraries = [
      import_node_path11.default.join(project, ".lake/build/lib/lean"),
      ...import_node_fs10.default.readdirSync(lease.packagesRoot).map((name) => import_node_path11.default.join(lease.packagesRoot, name, ".lake/build/lib/lean"))
    ].filter((file) => import_node_fs10.default.existsSync(file));
    import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(import_node_path11.default.join(project, output)), { recursive: true });
    signal?.throwIfAborted();
    const result2 = await runLeanProcess(readiness.leanPath, ["--json", "-j1", "-R", module2.sourceRoot, "-o", output, module2.file], {
      cwd: project,
      env: { ...env, LEAN_PATH: libraries.join(import_node_path11.default.delimiter), LEAN_NUM_THREADS: "1" },
      timeoutMs: Math.max(0, deadlineAt - Date.now()),
      signal,
      outputCapture: "head",
      outputLimit,
      stopGraceMs: 0
    });
    const cap = (text) => limitMathOutput(text, outputLimit, "head");
    return {
      ...result2,
      started: result2.started && !result2.errorCode,
      durationMs: Date.now() - startedAt,
      stdout: cap(result2.stdout),
      stderr: cap(result2.stderr + (result2.errorMessage ?? ""))
    };
  } finally {
    await lease.release();
  }
}
async function runLeanDiagnostics(input) {
  const outputLimit = input.outputLimit ?? 8e3;
  if (!Number.isSafeInteger(outputLimit) || outputLimit < 1 || outputLimit > 4e6)
    throw new Error("math_diagnostics_output_limit_invalid");
  const project = import_node_fs10.default.realpathSync(input.projectRoot);
  const env = resolveMathematicsRuntimeEnvironment(input.env || process.env);
  assertMathConstructionSources(project, input.files);
  const modules = mathLocalModuleBuildOrder(project, input.files);
  const excluded = new Set(input.excludedFiles ?? []);
  const cacheFile = import_node_path11.default.join(project, ".lake", "lean-diagnostics.json");
  assertMathCanonicalPath(cacheFile);
  let cache = {};
  try {
    const saved = JSON.parse(import_node_fs10.default.readFileSync(cacheFile, "utf8"));
    if (saved && typeof saved === "object" && !Array.isArray(saved)) cache = saved;
  } catch {
  }
  const configuration2 = () => LAKE_CONFIGURATION_FILES.map((file) => {
    const absolute = import_node_path11.default.join(project, file);
    return import_node_fs10.default.existsSync(absolute) ? mathDigest(import_node_fs10.default.readFileSync(absolute)) : "";
  });
  const config = configuration2();
  const { environmentDigest: environmentIdentity, toolIdentity } = leanDiagnosticEnvironmentIdentity(project, env);
  const sourceFiles = () => modules.map((module2) => [module2.file, mathDigest(import_node_fs10.default.readFileSync(import_node_path11.default.join(project, module2.file)))]);
  const initialSources = sourceFiles();
  const sourceIdentity = () => mathDigest(JSON.stringify([configuration2(), sourceFiles()]));
  const sourceDigest = sourceIdentity();
  const sources = [];
  const deadline = Date.now() + input.timeoutMs;
  const phases = [];
  const cap = (text) => {
    if (Buffer.byteLength(text) <= outputLimit) return text;
    const notice = "\n[truncated; inspect diagnosticArtifacts for captured output and completeness]";
    return limitMathOutput(text, Math.max(0, outputLimit - Buffer.byteLength(notice)), "head") + limitMathOutput(notice, outputLimit, "head");
  };
  const appendOutput = (previous, next) => cap(previous + (previous && !previous.endsWith("\n") && next ? "\n" : "") + next);
  const artifactDigest = (output) => mathDigest(JSON.stringify([
    output,
    output + ".private",
    output + ".server",
    output.replace(/\.olean$/u, ".ir"),
    output.replace(/\.olean$/u, ".ir.sig")
  ].map((file) => {
    assertMathCanonicalPath(file);
    return import_node_fs10.default.existsSync(file) ? mathDigest(import_node_fs10.default.readFileSync(file)) : null;
  })));
  let stdout = "", stderr = "";
  const messages = [], diagnosticArtifacts = [];
  const finish = (result2) => {
    const latest = import_node_path11.default.join(project, ".lake", "lean-diagnostics-latest.json");
    assertMathCanonicalPath(latest);
    import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(latest), { recursive: true, mode: 448 });
    writeMathJsonDurable(latest, {
      schema: "theoremos.lean-diagnostics-latest.v1",
      authority: "advisory-lean-process",
      sourceDigest,
      environmentDigest: environmentIdentity,
      toolIdentity,
      requestedFiles: [...input.files],
      configuration: LAKE_CONFIGURATION_FILES.map((file, index) => ({ file, digest: config[index] || null })),
      sourceFiles: initialSources.map(([file, digest3]) => ({ file, digest: digest3 })),
      exitCode: result2.exitCode,
      timedOut: result2.timedOut,
      aborted: result2.aborted ?? false,
      diagnosticArtifacts
    });
    return result2;
  };
  const captured = (reference2) => {
    try {
      if (!reference2 || typeof reference2.digest !== "string" || !/^[a-f0-9]{64}$/u.test(reference2.digest) || reference2.path !== `.lake/diagnostic-artifacts/${reference2.digest}.json` || reference2.environmentDigest !== environmentIdentity) return false;
      const file = import_node_path11.default.join(project, reference2.path);
      assertMathCanonicalPath(file);
      const text = import_node_fs10.default.readFileSync(file, "utf8");
      return mathDigest(text) === reference2.digest;
    } catch {
      return false;
    }
  };
  const messagePreview = (message) => ({
    ...message,
    message: cap(message.message),
    ...message.goalText ? { goalText: cap(message.goalText) } : {},
    truncated: Buffer.byteLength(message.message) > outputLimit
  });
  const summary = () => {
    const firstBlocking = messages.find((message) => message.severity === "error");
    const selected = [];
    let bytes = 0;
    for (const message of messages.slice(0, 64)) {
      const preview = messagePreview(message), size = Buffer.byteLength(JSON.stringify(preview));
      if (bytes + size > outputLimit) break;
      selected.push(preview);
      bytes += size;
    }
    return {
      sourceDigest,
      environmentDigest: environmentIdentity,
      firstBlocking: firstBlocking && messagePreview(firstBlocking),
      messages: selected,
      omittedMessages: messages.length - selected.length,
      diagnosticArtifacts,
      previewTruncated: selected.length < messages.length || Boolean(firstBlocking && Buffer.byteLength(firstBlocking.message) > outputLimit) || diagnosticArtifacts.some((reference2) => reference2.captureComplete === false) || /\[truncated;/u.test(stdout + stderr)
    };
  };
  const retain = (file, result2) => {
    const capturedComplete = (text2, hash3) => hash3 ? mathDigest(text2) === hash3 : null;
    const complete = [capturedComplete(result2.stdout, result2.stdoutSha256), capturedComplete(result2.stderr, result2.stderrSha256)];
    const captureComplete = complete.includes(false) ? false : complete.includes(null) ? null : true;
    const observed = [...parseLeanDiagnosticOutput(result2.stdout).messages, ...parseLeanDiagnosticOutput(result2.stderr).messages];
    const artifact = {
      schema: "theoremos.lean-diagnostics.v1",
      authority: "advisory-lean-process",
      sourceDigest,
      environmentDigest: environmentIdentity,
      toolIdentity,
      file,
      sourceCurrent: sourceIdentity() === sourceDigest,
      sourceFiles: initialSources.map(([file2, digest4]) => ({ file: file2, digest: digest4 })),
      exitCode: result2.exitCode,
      timedOut: result2.timedOut,
      aborted: result2.aborted ?? false,
      captureComplete,
      captureLimit: DIAGNOSTIC_CAPTURE_LIMIT,
      stdout: result2.stdout,
      stderr: result2.stderr,
      stdoutSha256: result2.stdoutSha256 ?? null,
      stderrSha256: result2.stderrSha256 ?? null,
      messages: observed
    };
    const text = canonicalMathJson(artifact), digest3 = mathDigest(text), relative = `.lake/diagnostic-artifacts/${digest3}.json`;
    const artifactFile = import_node_path11.default.join(project, relative);
    assertMathCanonicalPath(artifactFile);
    import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(artifactFile), { recursive: true, mode: 448 });
    writeMathJsonDurable(artifactFile, artifact);
    const reference2 = { path: relative, digest: digest3, sourceDigest, environmentDigest: environmentIdentity, captureComplete };
    diagnosticArtifacts.push(reference2);
    messages.push(...observed);
    return { reference: reference2, observed };
  };
  const quote = (value) => "'" + value.replaceAll("'", "'\\''") + "'";
  try {
    for (const module2 of modules) {
      input.signal?.throwIfAborted();
      sources.push(mathDigest(import_node_fs10.default.readFileSync(import_node_path11.default.join(project, module2.file))));
      if (input.dependenciesOnly && (input.files.includes(module2.file) || excluded.has(module2.file))) continue;
      const output = `.lake/build/lib/lean/${import_node_path11.default.posix.relative(module2.sourceRoot, module2.file).replace(/\.lean$/u, ".olean")}`;
      const absoluteOutput = import_node_path11.default.join(project, output);
      assertMathCanonicalPath(absoluteOutput);
      const digest3 = mathDigest(JSON.stringify([environmentIdentity, config, sources]));
      const saved = cache[module2.file];
      if (saved?.source === digest3 && import_node_fs10.default.existsSync(absoluteOutput) && saved.output === artifactDigest(absoluteOutput) && saved.diagnosticArtifact && captured(saved.diagnosticArtifact)) {
        phases.push({ file: module2.file, cached: true, durationMs: 0, exitCode: 0 });
        stdout = appendOutput(stdout, cap(typeof saved.stdout === "string" ? saved.stdout : ""));
        stderr = appendOutput(stderr, cap(typeof saved.stderr === "string" ? saved.stderr : ""));
        diagnosticArtifacts.push(saved.diagnosticArtifact);
        messages.push(...saved.messages ?? []);
        sources.push(saved.output);
        continue;
      }
      input.onProgress?.(module2.file);
      const remainingMs = deadline - Date.now();
      if (remainingMs <= 0) return finish({ exitCode: null, timedOut: true, stdout, stderr, phases, ...summary() });
      const result2 = env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV] ? await runWorkerLean(project, module2, output, env, remainingMs, input.signal, DIAGNOSTIC_CAPTURE_LIMIT) : await runMathematicsSandboxedCommand({
        checkoutRoot: project,
        command: "lake",
        args: ["env", "/bin/sh", "-ceu", `mkdir -p ${quote(import_node_path11.default.posix.dirname(output))}
exec lean --json -j1 -R ${quote(module2.sourceRoot)} -o ${quote(output)} ${quote(module2.file)}`],
        env,
        signal: input.signal,
        timeoutMs: remainingMs,
        outputCapture: "head",
        outputLimit: DIAGNOSTIC_CAPTURE_LIMIT
      });
      phases.push({ file: module2.file, cached: false, durationMs: result2.durationMs, exitCode: result2.exitCode });
      const retained = retain(module2.file, result2);
      if (sourceIdentity() !== sourceDigest) return finish({
        exitCode: 1,
        timedOut: false,
        stdout: cap(renderLeanDiagnosticOutput(result2.stdout)),
        stderr: "math_diagnostics_source_changed: saved sources changed during compilation",
        phases,
        ...summary()
      });
      const moduleStdout = cap(renderLeanDiagnosticOutput(result2.stdout)), moduleStderr = cap(renderLeanDiagnosticOutput(result2.stderr));
      stdout = appendOutput(stdout, moduleStdout);
      stderr = appendOutput(stderr, moduleStderr);
      if (result2.exitCode !== 0 || result2.timedOut || result2.aborted || !result2.started) return finish({
        ...result2,
        stdout: moduleStdout,
        stderr: moduleStderr,
        phases,
        ...summary()
      });
      if (import_node_fs10.default.existsSync(absoluteOutput)) {
        const artifact = artifactDigest(absoluteOutput);
        cache[module2.file] = {
          source: digest3,
          output: artifact,
          stdout: renderLeanDiagnosticOutput(result2.stdout),
          stderr: renderLeanDiagnosticOutput(result2.stderr),
          diagnosticArtifact: retained.reference,
          messages: retained.observed
        };
        sources.push(artifact);
        import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(cacheFile), { recursive: true });
        import_node_fs10.default.writeFileSync(cacheFile, JSON.stringify(cache) + "\n", { mode: 384 });
      }
    }
    if (sourceIdentity() !== sourceDigest) return finish({
      exitCode: 1,
      timedOut: false,
      stdout,
      stderr: "math_diagnostics_source_changed: saved sources changed during diagnostics",
      phases,
      ...summary()
    });
    return finish({ exitCode: 0, timedOut: false, stdout, stderr, phases, ...summary() });
  } catch (error) {
    try {
      finish({ exitCode: null, timedOut: error instanceof Error && error.name === "TimeoutError", aborted: input.signal?.aborted });
    } catch {
    }
    throw error;
  }
}
function bindLeanPackages(project, authorizedPackagesRoot) {
  const root = import_node_fs10.default.realpathSync(authorizedPackagesRoot);
  if (!import_node_fs10.default.statSync(root).isDirectory()) throw new Error("math_lean_packages_not_directory");
  const packages = import_node_path11.default.join(project, ".lake", "packages");
  assertMathCanonicalPath(import_node_path11.default.dirname(packages));
  import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(packages), { recursive: true });
  const existing = import_node_fs10.default.lstatSync(packages, { throwIfNoEntry: false });
  if (existing?.isSymbolicLink()) {
    if (import_node_path11.default.resolve(import_node_path11.default.dirname(packages), import_node_fs10.default.readlinkSync(packages)) === root) return;
    import_node_fs10.default.unlinkSync(packages);
  } else if (existing) {
    if (!existing.isDirectory()) throw new Error("math_lean_packages_not_directory");
    return;
  }
  import_node_fs10.default.symlinkSync(root, packages, "dir");
}
function prepareLeanDiagnosticOverrides(project) {
  const manifestFile = import_node_path11.default.join(project, "lake-manifest.json");
  if (!import_node_fs10.default.existsSync(manifestFile)) return;
  const manifest = JSON.parse(import_node_fs10.default.readFileSync(manifestFile, "utf8"));
  const packages = manifest.packages.map((entry) => {
    const name = entry.name.replace(/^«(.+)»$/u, "$1");
    if (!name || /[/\\\0]/u.test(name) || name === "." || name === "..") throw new Error("math_invalid_package_name");
    return { ...entry, type: "path", dir: import_node_path11.default.join(project, ".lake", "packages", name) };
  });
  const file = import_node_path11.default.join(project, ".lake", "package-overrides.json");
  assertMathCanonicalPath(file);
  import_node_fs10.default.mkdirSync(import_node_path11.default.dirname(file), { recursive: true });
  import_node_fs10.default.writeFileSync(file, JSON.stringify({ schemaVersion: "1.2.0", packages }) + "\n", { mode: 384 });
}

// src/math/leanTypeDiagnostics.ts
var import_node_crypto5 = __toESM(require("node:crypto"));
var import_node_fs11 = __toESM(require("node:fs"));
var import_node_path12 = __toESM(require("node:path"));
function leanTypeDiagnosticCommands(type, output, application) {
  return [
    "set_option autoImplicit false",
    "set_option pp.fullNames true",
    "run_cmd Lean.Elab.Command.liftTermElabM do",
    `  let parsed <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") ${JSON.stringify(type)} with`,
    "    | .ok stx => pure stx",
    '    | .error message => throwError "{message}"',
    "  let expression <- Lean.Elab.Term.elabType parsed",
    "  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing",
    "  let expression <- Lean.instantiateMVars expression",
    "  if expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then",
    '    throwError "Requested type must be closed without free variables or metavariables"',
    "  let rendered := (<- Lean.Meta.ppExpr expression).pretty",
    '  if rendered.utf8ByteSize > 24000 then throwError "Elaborated type exceeds its export bound"',
    ...application === void 0 ? ['  let report := Lean.Json.mkObj [("type", Lean.toJson rendered)]'] : [
      `  let term <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") ${JSON.stringify(application)} with`,
      "    | .ok stx => pure stx",
      '    | .error message => throwError "{message}"',
      "  let applied <- Lean.Elab.Term.elabTermEnsuringType term expression",
      "  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing",
      "  let applied <- Lean.instantiateMVars applied",
      "  if applied.hasMVar || applied.hasFVar || applied.hasLooseBVars then",
      '    throwError "Application must be closed without free variables or metavariables"',
      "  let constants := applied.getUsedConstants.toList.map Lean.Name.toString",
      '  if constants.contains "sorryAx" then throwError "Application contains an admitted term"',
      '  if constants.length > 4096 then throwError "Application reference export exceeds its bound"',
      '  let report := Lean.Json.mkObj [("type", Lean.toJson rendered), ("constants", Lean.toJson constants)]'
    ],
    `  Lean.Core.liftIOCore <| IO.FS.writeFile ${JSON.stringify(output)} report.compress`
  ].join("\n");
}
function leanTypeDiagnosticProjection(input) {
  const context = leanDeclarationContextCommands(input.files.find((file) => file.file === input.file).source, input.context);
  const module2 = input.modules.find((module3) => module3.file === input.file).module;
  if (!/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(module2))
    throw new Error("math_type_diagnostics_module_invalid");
  const files = input.files.map((file) => {
    let source = file.source;
    if (file.file.endsWith(".lean") && file.file !== "lakefile.lean") {
      for (const region of inspectLeanDeclarationRegions(source).reverse())
        if (/^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset)))
          source = source.slice(0, region.bodyOffset) + " by sorry\n" + source.slice(region.endOffset);
    }
    return { file: file.file, source };
  });
  const query = "TypeDiagnostic.lean", output = ".lake/type-diagnostic.json";
  const commands = [
    "import Lean",
    `import ${module2}`,
    ...context.before,
    leanTypeDiagnosticCommands(input.type, output, input.expression),
    ...context.after
  ].join("\n") + "\n";
  const digest3 = mathDigest(canonicalMathJson({
    schema: "theoremos.lean-type-projection.v1",
    modules: input.modules,
    files: files.map(({ file, source }) => ({ file, digest: mathDigest(source) })),
    query,
    commands
  }));
  return { files, query, output, commands, digest: digest3 };
}
async function checkLeanType(input) {
  if (!input.type.trim() || Buffer.byteLength(input.type) > 12e3 || !input.context.trim() || input.context.length > 1e3 || input.expression !== void 0 && (!input.expression.trim() || Buffer.byteLength(input.expression) > 12e3))
    throw new Error("math_type_diagnostics_input_invalid");
  const project = import_node_fs11.default.realpathSync(input.projectRoot);
  const env = resolveMathematicsRuntimeEnvironment(input.env ?? process.env);
  const sealed = resolveMathProofEnvironment(project, env);
  const environment = leanDiagnosticEnvironmentIdentity(project, env);
  assertMathConstructionSources(project, [input.file]);
  const modules = mathLocalModuleBuildOrder(project, input.file);
  const files = [...modules.map((module2) => module2.file), ...LAKE_CONFIGURATION_FILES.filter((file) => import_node_fs11.default.existsSync(import_node_path12.default.join(project, file)))];
  const snapshot2 = files.map((file) => {
    const source = import_node_path12.default.join(project, file);
    assertMathCanonicalPath(source);
    const read = readMathFile(source, 4e6);
    return { file, source: read.bytes.toString("utf8"), digest: mathDigest(read.bytes), identity: read.identity };
  });
  const sourceDigest = mathDigest(canonicalMathJson(snapshot2.map(({ file, digest: digest3 }) => ({ file, digest: digest3 }))));
  const projection = leanTypeDiagnosticProjection({
    files: snapshot2,
    modules,
    file: input.file,
    context: input.context,
    type: input.type,
    expression: input.expression
  });
  const directory = import_node_path12.default.join(project, ".lake", "type-diagnostics", import_node_crypto5.default.randomUUID()), clone = import_node_path12.default.join(directory, "project");
  assertMathCanonicalPath(clone);
  import_node_fs11.default.mkdirSync(clone, { recursive: true, mode: 448 });
  for (const file of projection.files) {
    const target = import_node_path12.default.join(clone, file.file);
    assertMathCanonicalPath(target);
    import_node_fs11.default.mkdirSync(import_node_path12.default.dirname(target), { recursive: true, mode: 448 });
    import_node_fs11.default.writeFileSync(target, file.source, { mode: 384 });
  }
  for (const file of snapshot2) {
    const current = readMathFile(import_node_path12.default.join(project, file.file), 4e6);
    if (current.identity !== file.identity || mathDigest(current.bytes) !== file.digest) throw new Error("math_type_diagnostics_source_changed");
  }
  const packages = sealed?.packagesRoot ?? import_node_path12.default.join(project, ".lake", "packages");
  if (import_node_fs11.default.existsSync(packages)) bindLeanPackages(clone, packages);
  prepareLeanDiagnosticOverrides(clone);
  if (sealed) {
    sealed.verify();
    if (resolveMathProofEnvironment(clone, env)?.identity !== sealed.identity)
      throw new Error("math_type_diagnostics_environment_changed");
  }
  import_node_fs11.default.writeFileSync(import_node_path12.default.join(clone, projection.query), projection.commands, { mode: 384 });
  const diagnostics = await runLeanDiagnostics({
    projectRoot: clone,
    files: [projection.query],
    env,
    signal: input.signal,
    timeoutMs: input.timeoutMs,
    onProgress: input.onProgress
  });
  for (const file of snapshot2) {
    const current = readMathFile(import_node_path12.default.join(project, file.file), 4e6);
    if (current.identity !== file.identity || mathDigest(current.bytes) !== file.digest) throw new Error("math_type_diagnostics_source_changed");
  }
  if (canonicalMathJson(mathLocalModuleBuildOrder(project, input.file)) !== canonicalMathJson(modules) || canonicalMathJson(LAKE_CONFIGURATION_FILES.filter((file) => import_node_fs11.default.existsSync(import_node_path12.default.join(project, file)))) !== canonicalMathJson(files.filter((file) => LAKE_CONFIGURATION_FILES.includes(file))) || canonicalMathJson(leanDiagnosticEnvironmentIdentity(project, env)) !== canonicalMathJson(environment))
    throw new Error("math_type_diagnostics_environment_or_sources_changed");
  sealed?.verify();
  let elaboratedType, constants;
  if (diagnostics.exitCode === 0 && !diagnostics.timedOut) {
    const value = readMathJson(import_node_path12.default.join(clone, projection.output));
    if (typeof value.type !== "string" || !value.type.trim() || Buffer.byteLength(value.type) > 24e3)
      throw new Error("math_type_diagnostics_export_invalid");
    elaboratedType = value.type;
    if (input.expression !== void 0) {
      if (!Array.isArray(value.constants) || value.constants.length > 4096 || value.constants.some((item) => typeof item !== "string" || item.length > 1e3))
        throw new Error("math_type_diagnostics_export_invalid");
      constants = value.constants;
    }
  }
  const evidence = input.expression === void 0 ? "advisory-type-elaboration" : "advisory-application-elaboration";
  const manifest = {
    schema: "theoremos.lean-type-diagnostics.v1",
    authority: evidence,
    proofAcceptance: "not-assessed",
    sourceDigest,
    projectionDigest: projection.digest,
    queryDigest: mathDigest(projection.commands),
    files: snapshot2.map(({ file, digest: digest3 }) => ({ file, digest: digest3 })),
    context: input.context,
    requestedType: input.type,
    ...input.expression !== void 0 ? { requestedExpression: input.expression, constants } : {},
    environment,
    elaboratedType,
    diagnostics
  };
  const artifactFile = import_node_path12.default.join(directory, "manifest.json");
  writeMathJsonDurable(artifactFile, manifest);
  return {
    ...diagnostics,
    status: elaboratedType ? "elaborated" : "failed",
    type: elaboratedType,
    sourceSnapshotDigest: sourceDigest,
    projectionDigest: projection.digest,
    context: input.context,
    sourceFiles: snapshot2.map(({ file, digest: digest3 }) => ({ file, digest: digest3 })),
    environment,
    ...input.expression !== void 0 ? { expression: input.expression, constants } : {},
    artifact: { path: import_node_path12.default.relative(project, artifactFile).replaceAll(import_node_path12.default.sep, "/"), digest: mathDigest(canonicalMathJson(manifest)) },
    diagnosticArtifacts: diagnostics.diagnosticArtifacts.map((reference2) => ({
      ...reference2,
      path: import_node_path12.default.relative(project, import_node_path12.default.join(clone, reference2.path)).replaceAll(import_node_path12.default.sep, "/")
    })),
    evidence,
    proofAcceptance: "not-assessed"
  };
}

// src/solver/problem.ts
var import_node_fs12 = __toESM(require("node:fs"));
var import_node_path13 = __toESM(require("node:path"));

// src/math/imo2026Adapter.ts
var IMO2026_SUPPORTED_PROBLEMS = Object.freeze([
  "imo2026_q1",
  "imo2026_q2",
  "imo2026_q3",
  "imo2026_q4",
  "imo2026_q5",
  "imo2026_q6"
]);
var PROBLEM_NUMBER = Object.freeze({
  imo2026_q1: "Q1",
  imo2026_q2: "Q2",
  imo2026_q3: "Q3",
  imo2026_q4: "Q4",
  imo2026_q5: "Q5",
  imo2026_q6: "Q6"
});
var EXPECTED_THEOREMS = Object.freeze({
  imo2026_q1: Object.freeze([
    "statement_a_termination",
    "statement_a_unique_large",
    "statement_b_invariance",
    "terminal_value_eq_Mval",
    "Mval_gt_one"
  ]),
  imo2026_q2: Object.freeze(["main_theorem"]),
  imo2026_q3: Object.freeze([
    "pieceLengths_sum",
    "pieceLengths_length",
    "L_mem_Icc",
    "V_eq",
    "lower_bound",
    "upper_bound"
  ]),
  imo2026_q4: Object.freeze(["main_theorem"]),
  imo2026_q5: Object.freeze(["main_theorem"]),
  imo2026_q6: Object.freeze(["main_theorem"])
});
var EXPECTED_TRUSTED_FILES = Object.freeze([
  "Challenge.lean",
  "lakefile.lean",
  "lakefile.toml",
  "lake-manifest.json",
  "lean-toolchain",
  "MathFlowBench/CacheWarm.lean",
  "MathFlowBench/DeepScientistGenerated/A_probe/Probe.lean",
  "docs/humanize/math-contract.json"
]);
var IMO2026_LAKEFILE_TOML = [
  'name = "IMO2026Humanize"',
  'defaultTargets = ["Submission"]',
  "",
  "[leanOptions]",
  "autoImplicit = false",
  "",
  "[[require]]",
  'name = "mathlib"',
  'git = "https://github.com/leanprover-community/mathlib4.git"',
  'rev = "v4.31.0"',
  "",
  "[[lean_lib]]",
  'name = "MathFlowBench"',
  'srcDir = "MathFlowBench"',
  "",
  "[[lean_lib]]",
  'name = "Submission"',
  ""
].join("\n");

// src/math/leanEvalCatalogAdapter.ts
var LEAN_EVAL_LEADERBOARD_URL = "https://leanprover.github.io/lean-eval-leaderboard/site-data/v2/groups/formalization-evaluation.json";

// src/math/leanEvalAdapter.ts
var LEAN_EVAL_PERMITTED_AXIOMS = Object.freeze(["Classical.choice", "Quot.sound", "propext"]);
var REQUIRED_TRUSTED_FILES = Object.freeze([
  "Challenge.lean",
  "Solution.lean",
  "WorkspaceTest.lean",
  "config.json",
  "holes.json",
  "lakefile.toml",
  "lean-toolchain"
]);
var MAX_GIT_OUTPUT_BYTES = 64 * 1024 * 1024;
var MAX_TRACKED_FILE_BYTES = 16 * 1024 * 1024;

// src/math/leanEvalBootstrap.ts
var receiptHash = external_exports.string().regex(/^[0-9a-f]{64}$/iu);
var positiveTime = external_exports.number().finite().positive();
var nonBlank = (value) => !!value.trim();
var bootstrapReceiptSchema = external_exports.object({
  schema: external_exports.literal("deepscientist.mathematics.lean-eval-bootstrap-receipt.v1"),
  receiptId: external_exports.string().refine(nonBlank),
  problemId: external_exports.string().regex(/^[A-Za-z0-9_.-]+$/u),
  evaluationMode: external_exports.enum(["official", "benchmark"]).optional(),
  catalogHash: receiptHash,
  leaderboardSource: external_exports.string().refine(nonBlank),
  leaderboardHash: receiptHash.optional(),
  leaderboardGeneratedAt: positiveTime.optional(),
  workspaceRoot: external_exports.string(),
  projectRoot: external_exports.string(),
  verifierProjectRoot: external_exports.string().optional(),
  sourceProjectRoot: external_exports.string().optional(),
  activeProblemPath: external_exports.string(),
  contract: external_exports.object({}).passthrough(),
  solverOwnedFiles: external_exports.array(external_exports.unknown()),
  trustedFiles: external_exports.array(external_exports.unknown()),
  createdAt: positiveTime
}).passthrough().refine((receipt) => receipt.leaderboardSource !== LEAN_EVAL_LEADERBOARD_URL || receipt.leaderboardHash !== void 0 && receipt.leaderboardGeneratedAt !== void 0);
var publicObligationsSchema = external_exports.array(external_exports.object({ name: external_exports.string().refine(nonBlank), declarationHash: external_exports.string().regex(/^[a-f0-9]{64}$/u) }));

// src/math/localExample.ts
var LOCAL_EXAMPLE_TOOLCHAIN = "leanprover/lean4:v4.33.0";
var LOCAL_EXAMPLE_STATEMENT = "namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by sorry\n\ntheorem zero_add (n : Nat) : 0 + n = n := by sorry\n\nend Tutorial\n";
var LOCAL_EXAMPLE_PROOF = LOCAL_EXAMPLE_STATEMENT.replace("by sorry", "by rfl").replace("by sorry", "by exact Nat.zero_add n");
var LOCAL_EXAMPLE_FAILED_PROOF = LOCAL_EXAMPLE_STATEMENT.replaceAll("by sorry", "by rfl");
var trustedSources = {
  "Challenge.lean": LOCAL_EXAMPLE_STATEMENT,
  "lean-toolchain": `${LOCAL_EXAMPLE_TOOLCHAIN}
`,
  "lakefile.toml": 'name = "theorem_os_tutorial"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Submission"\n',
  "lake-manifest.json": JSON.stringify({ version: "1.1.0", packagesDir: ".lake/packages", packages: [], name: "theorem_os_tutorial", lakeDir: ".lake" }) + "\n"
};
var receiptSchema = external_exports.object({
  schema: external_exports.literal("theorem-os.local-example.v1"),
  workspaceRoot: external_exports.string(),
  projectRoot: external_exports.string(),
  activeProblemPath: external_exports.string(),
  contract: external_exports.record(external_exports.unknown()),
  trustedFiles: external_exports.array(external_exports.string()),
  solverOwnedFiles: external_exports.array(external_exports.string()),
  publicObligations: external_exports.array(external_exports.object({ name: external_exports.string(), declarationHash: external_exports.string() }).strict())
}).strict();

// resources/mathlib/environment.json
var environment_default = {
  schema: "theorem-os.lean-task-mathlib.v1",
  id: "mathlib",
  toolchain: "leanprover/lean4:v4.33.0",
  mathlibRevision: "db584cd6d46c92f209a44c0f1c829460d327499d",
  lakefile: 'name = "theorem_os_problem"\nversion = "0.1.0"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "db584cd6d46c92f209a44c0f1c829460d327499d"\n\n[[lean_lib]]\nname = "Submission"\n',
  manifest: {
    version: "1.2.0",
    packagesDir: ".lake/packages",
    packages: [
      {
        url: "https://github.com/leanprover-community/plausible",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "b7eb3304aeae834b12dda98993a37f6a41f6f0bb",
        name: "plausible",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/LeanSearchClient",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "5f4d51b81cbd3f6b32b156bfad9056621a040404",
        name: "LeanSearchClient",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/import-graph",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "16f02aa7642864af59f1ff0e384a015994db9118",
        name: "importGraph",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/ProofWidgets4",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957",
        name: "proofwidgets",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.lean"
      },
      {
        url: "https://github.com/leanprover-community/aesop",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e",
        name: "aesop",
        manifestFile: "lake-manifest.json",
        inputRev: "master",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/quote4",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "92c15be17b7caf78c2ad767ec40f89052d908d81",
        name: "Qq",
        manifestFile: "lake-manifest.json",
        inputRev: "master",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/batteries",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d",
        name: "batteries",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover/lean4-cli",
        type: "git",
        subDir: null,
        scope: "leanprover",
        rev: "6130a47896ce867c6a4a55373441e59e565bad0f",
        name: "Cli",
        manifestFile: "lake-manifest.json",
        inputRev: "v4.33.0",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/mathlib4.git",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "db584cd6d46c92f209a44c0f1c829460d327499d",
        name: "mathlib",
        manifestFile: "lake-manifest.json",
        inputRev: "db584cd6d46c92f209a44c0f1c829460d327499d",
        inherited: false,
        configFile: "lakefile.lean"
      }
    ],
    name: "theorem_os_problem",
    lakeDir: ".lake",
    fixedToolchain: true
  }
};

// resources/openai-math/environment.json
var environment_default2 = {
  schema: "theorem-os.lean-task-mathlib.v1",
  id: "openai-math",
  toolchain: "leanprover/lean4:v4.34.1",
  mathlibRevision: "d13f23b723b8a846827a245b89c10fc7d3f11612",
  lakefile: 'name = "theorem_os_problem"\nversion = "0.1.0"\ndefaultTargets = ["Submission"]\n\n[leanOptions]\nautoImplicit = false\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "d13f23b723b8a846827a245b89c10fc7d3f11612"\n\n[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Submission"\n',
  manifest: {
    version: "1.2.0",
    packagesDir: ".lake/packages",
    packages: [
      {
        url: "https://github.com/leanprover-community/plausible",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "118aa17ee84656b8bd727fef7c458ee8c833385c",
        name: "plausible",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/LeanSearchClient",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "ddf04cf3949fa556442341e87d47f9f6e6074707",
        name: "LeanSearchClient",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/import-graph",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "e928b72544873815af278d38681b31c0293588e3",
        name: "importGraph",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/ProofWidgets4",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
        name: "proofwidgets",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.lean"
      },
      {
        url: "https://github.com/leanprover-community/aesop",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "355695d523e41d0554926416cba2a2b3544fbbc9",
        name: "aesop",
        manifestFile: "lake-manifest.json",
        inputRev: "master",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/quote4",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
        name: "Qq",
        manifestFile: "lake-manifest.json",
        inputRev: "master",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/batteries",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
        name: "batteries",
        manifestFile: "lake-manifest.json",
        inputRev: "main",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover/lean4-cli",
        type: "git",
        subDir: null,
        scope: "leanprover",
        rev: "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
        name: "Cli",
        manifestFile: "lake-manifest.json",
        inputRev: "v4.34.0",
        inherited: true,
        configFile: "lakefile.toml"
      },
      {
        url: "https://github.com/leanprover-community/mathlib4.git",
        type: "git",
        subDir: null,
        scope: "leanprover-community",
        rev: "d13f23b723b8a846827a245b89c10fc7d3f11612",
        name: "mathlib",
        manifestFile: "lake-manifest.json",
        inputRev: "d13f23b723b8a846827a245b89c10fc7d3f11612",
        inherited: false,
        configFile: "lakefile.lean"
      }
    ],
    name: "theorem_os_problem",
    lakeDir: ".lake",
    fixedToolchain: true
  }
};

// src/math/leanTaskEnvironment.ts
var standardFiles = Object.freeze({
  "lean-toolchain": `${LOCAL_EXAMPLE_TOOLCHAIN}
`,
  "lakefile.toml": 'name = "theorem_os_problem"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Submission"\n',
  "lake-manifest.json": JSON.stringify({
    version: "1.1.0",
    packagesDir: ".lake/packages",
    packages: [],
    name: "theorem_os_problem",
    lakeDir: ".lake"
  }) + "\n"
});
function configuration(id, toolchain, files, mathlibRevision) {
  return Object.freeze({
    id,
    toolchain,
    files,
    ...mathlibRevision ? { mathlibRevision } : {},
    dependencyDigest: mathDigest(canonicalMathJson({
      schema: "theorem-os.lean-task-environment.v1",
      id,
      toolchain,
      files,
      ...mathlibRevision ? { mathlibRevision } : {}
    }))
  });
}
var standard = configuration("standard", LOCAL_EXAMPLE_TOOLCHAIN, standardFiles);
var gitRevision = external_exports.string().regex(/^[0-9a-f]{40}$/u);
function pinnedMathlibEnvironment(raw, id, toolchain) {
  const resource = external_exports.object({
    schema: external_exports.literal("theorem-os.lean-task-mathlib.v1"),
    id: external_exports.literal(id),
    toolchain: external_exports.literal(toolchain),
    mathlibRevision: gitRevision,
    lakefile: external_exports.string().min(1),
    manifest: external_exports.object({
      version: external_exports.literal("1.2.0"),
      packagesDir: external_exports.literal(".lake/packages"),
      packages: external_exports.array(external_exports.object({
        url: external_exports.string().url().startsWith("https://github.com/"),
        type: external_exports.literal("git"),
        subDir: external_exports.null(),
        scope: external_exports.string().min(1),
        rev: gitRevision,
        name: external_exports.string().regex(/^[A-Za-z_][A-Za-z0-9_]*$/u),
        manifestFile: external_exports.literal("lake-manifest.json"),
        inputRev: external_exports.string().min(1),
        inherited: external_exports.boolean(),
        configFile: external_exports.enum(["lakefile.toml", "lakefile.lean"])
      }).strict()).min(1),
      name: external_exports.literal("theorem_os_problem"),
      lakeDir: external_exports.literal(".lake"),
      fixedToolchain: external_exports.literal(true)
    }).strict()
  }).strict().parse(raw);
  const rootPackage = resource.manifest.packages.find((item) => item.name === "mathlib");
  const lakefile = parse(resource.lakefile);
  const requirements = lakefile.require;
  if (!rootPackage || rootPackage.rev !== resource.mathlibRevision || rootPackage.inputRev !== resource.mathlibRevision || rootPackage.url !== "https://github.com/leanprover-community/mathlib4.git" || rootPackage.inherited || rootPackage.configFile !== "lakefile.lean" || requirements?.length !== 1 || requirements[0]?.name !== "mathlib" || requirements[0]?.git !== rootPackage.url || requirements[0]?.rev !== resource.mathlibRevision || new Set(resource.manifest.packages.map((item) => item.name)).size !== resource.manifest.packages.length || resource.manifest.packages.some((item) => item.name !== "mathlib" && !item.inherited))
    throw new Error("lean_task_mathlib_resource_invalid");
  return configuration(id, resource.toolchain, Object.freeze({
    "lean-toolchain": `${resource.toolchain}
`,
    "lakefile.toml": resource.lakefile,
    "lake-manifest.json": JSON.stringify(resource.manifest, null, 2) + "\n"
  }), resource.mathlibRevision);
}
var mathlib = pinnedMathlibEnvironment(environment_default, "mathlib", LOCAL_EXAMPLE_TOOLCHAIN);
var openaiMath = pinnedMathlibEnvironment(environment_default2, "openai-math", "leanprover/lean4:v4.34.1");
if (openaiMath.mathlibRevision !== "d13f23b723b8a846827a245b89c10fc7d3f11612")
  throw new Error("openai_math_revision_changed");

// src/math/leanTask.ts
var LEAN_TASK_SOURCE_MAX_BYTES = 128 * 1024;
var LEAN_TASK_DESCRIPTION_MAX_LENGTH = 8e3;
var schema = "theorem-os.lean-task.v1";
var hash2 = external_exports.string().regex(/^[0-9a-f]{64}$/u);
var inputSchema = external_exports.object({
  source: external_exports.string().min(1).max(LEAN_TASK_SOURCE_MAX_BYTES),
  task: external_exports.string().trim().min(1).max(LEAN_TASK_DESCRIPTION_MAX_LENGTH),
  environment: external_exports.enum(["standard", "mathlib", "openai-math"]).optional(),
  definitionTargets: external_exports.array(external_exports.string().min(1)).max(256).optional()
}).strict();
var declarationSchema = external_exports.object({
  name: external_exports.string().min(1),
  kind: external_exports.enum(["theorem", "definition", "instance"]),
  declarationHash: hash2
}).strict();
var obligationSchema = external_exports.object({ name: external_exports.string().min(1), declarationHash: hash2 }).strict();
var receiptSchema2 = external_exports.object({
  schema: external_exports.literal(schema),
  kind: external_exports.literal("lean-task"),
  workspaceRoot: external_exports.string(),
  projectRoot: external_exports.string(),
  activeProblemPath: external_exports.string(),
  baseCommit: external_exports.string().regex(/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u),
  toolchain: external_exports.string().min(1),
  environment: inputSchema.shape.environment,
  environmentDigest: hash2.optional(),
  contract: external_exports.record(external_exports.unknown()),
  trustedFiles: external_exports.array(external_exports.string()),
  solverOwnedFiles: external_exports.array(external_exports.string()),
  publicObligations: external_exports.array(obligationSchema),
  declarations: external_exports.array(declarationSchema)
}).strict();
var seedSchema = external_exports.object({
  schema: external_exports.literal("theorem-os.lean-task-seed.v1"),
  task: inputSchema.shape.task,
  sourceHash: hash2,
  environment: inputSchema.shape.environment,
  environmentDigest: hash2.optional(),
  definitionTargets: inputSchema.shape.definitionTargets
}).strict();

// src/solver/problem.ts
var SolverSourceError = class extends Error {
  constructor(proofPath, reason, declarationName) {
    super(reason);
    this.proofPath = proofPath;
    this.declarationName = declarationName;
  }
  get recovery() {
    if (this.message === "math_local_module_import_cycle")
      return "Remove the added local import that creates a cycle. Shared helpers may import frozen dependencies, but cannot import a module that imports them. Preserve the saved proof work.";
    return this.message === "math_original_context_changed" ? "Restore the original imports, namespace/section placement, variables, opens, scopes and options from the seed commit. Keep new helpers; move helper-specific scopes and instances inside their proofs. Added imports may use explicit Mathlib.* modules or frozen local modules already imported by the original owned sources; avoid import cycles." : `Restore the original name, parameters, type and any frozen proof or definition body${this.declarationName ? ` of ${this.declarationName}` : ""} from the seed commit. Preserve new proof work.`;
  }
};
function solverMathlibImports(source) {
  return mathConstructionImports(source).filter((module2) => /^Mathlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+$/u.test(module2));
}
function solverProofImports(problem, source) {
  const local = new Set(Object.values(problem.sourceImports ?? {}).flat().filter((module2) => {
    const file = module2.replaceAll(".", "/") + ".lean";
    return isAllowedMathProofSource(file) && Object.hasOwn(problem.trustedFiles, file);
  }));
  return mathConstructionImports(source).filter((module2) => local.has(module2) || /^Mathlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+$/u.test(module2));
}
function isInstanceQuery(line) {
  const query = /^#synth[ \t]+[\p{L}_][\p{L}\p{M}\p{N}_'.]*(.*)$/u.exec(line);
  if (!query || /["`#;]/u.test(query[1])) return false;
  let depth = 0;
  let bare = "";
  const validBare = () => !bare || /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$|^[0-9]+$/u.test(bare) && !/^(?:import|public|private|meta|namespace|section|end|theorem|lemma|def|example|abbrev|opaque|instance|inductive|structure|class|axiom|constant|variable|universe|open|export|set_option|attribute|noncomputable|unsafe|syntax|macro|elab|notation|infix|infixl|infixr|prefix|postfix|initialize|builtin_initialize)$/u.test(bare);
  for (const character of query[1]) {
    if (character === "(") {
      if (!depth && !validBare()) return false;
      bare = "";
      depth++;
    } else if (character === ")") {
      if (--depth < 0) return false;
    } else if (!depth) {
      if (character === " " || character === "	") {
        if (!validBare()) return false;
        bare = "";
      } else bare += character;
    }
  }
  return depth === 0 && validBare();
}
function sourceStructure(source, originalNames, originalImports, allowedImports = solverMathlibImports(source)) {
  const addedImports = new Set(originalImports === void 0 ? [] : allowedImports.filter((module2) => !originalImports.includes(module2)));
  const regions = inspectLeanDeclarationRegions(source);
  let frozen = "";
  let cursor = 0;
  for (const region of regions) {
    const context = source.slice(cursor, region.startOffset);
    frozen += originalNames.has(region.name) ? context : context.replace(/\bnoncomputable[ \t]+$/u, "");
    if (originalNames.has(region.name)) frozen += `${region.declarationType}
`;
    cursor = region.endOffset;
  }
  frozen += source.slice(cursor);
  return mathDigest(frozen.split("\n").map((line) => line.trim()).filter((line) => line && !addedImports.has(/^import[ \t]+([^ \t]+)$/u.exec(line)?.[1] ?? "") && !/^#check[ \t]+[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(line) && !isInstanceQuery(line)).join("\n"));
}
function assertSolverProjectSources(problem, project) {
  let addedLocalImportFile;
  for (const [relative, digest3] of Object.entries(problem.trustedFiles)) {
    const target = import_node_path13.default.join(project, relative);
    assertMathCanonicalPath(target);
    if (mathDigest(import_node_fs12.default.readFileSync(target)) !== digest3) throw new Error("math_trusted_source_changed");
  }
  for (const [relative, originals] of Object.entries(problem.declarations)) {
    const file = import_node_path13.default.join(project, relative);
    assertMathCanonicalPath(file);
    const source = import_node_fs12.default.readFileSync(file, "utf8");
    const regions = inspectLeanDeclarationRegions(source);
    for (const original of originals) {
      const matches = regions.filter((item) => item.name === original.name);
      const current = matches[0];
      if (matches.length !== 1 || current.declarationType !== original.header || original.body && mathDigest(source.slice(current.bodyOffset, current.endOffset).trim()) !== original.body)
        throw new SolverSourceError(relative, "math_original_declaration_changed", original.name);
    }
    const allowedImports = solverProofImports(problem, source);
    if (allowedImports.some((module2) => !module2.startsWith("Mathlib.") && !problem.sourceImports?.[relative]?.includes(module2)))
      addedLocalImportFile = relative;
    if (sourceStructure(source, new Set(originals.map((item) => item.name)), problem.sourceImports?.[relative], allowedImports) !== problem.sourceStructure[relative])
      throw new SolverSourceError(relative, "math_original_context_changed");
  }
  if (addedLocalImportFile) {
    try {
      mathLocalModuleBuildOrder(project, Object.keys(problem.declarations));
    } catch (error) {
      if (error instanceof Error && error.message === "math_local_module_import_cycle")
        throw new SolverSourceError(addedLocalImportFile, "math_local_module_import_cycle");
      throw error;
    }
  }
}

// scripts/mathematics/checkLean.ts
async function main() {
  const args = process.argv.slice(2);
  if (args[0] === "check-lean") args.shift();
  const { values } = (0, import_node_util.parseArgs)({ args, options: {
    workspace: { type: "string" },
    file: { type: "string", multiple: true },
    type: { type: "string" },
    context: { type: "string" },
    expression: { type: "string" },
    "timeout-seconds": { type: "string", default: "0" },
    help: { type: "boolean" }
  } });
  if (values.help) console.log("Usage: theorem-os check-lean --workspace DIR --file FILE [--file FILE --timeout-seconds N]\nOptional: --type TYPE --context DECLARATION elaborates one closed type in a proof-erased snapshot of the single --file context.\nAdd --expression TERM to check one selected closed application against that type. Local theorem bodies are erased; this is advisory sufficiency, not proof acceptance.\nChecks saved sources against pinned packages. Timeout 0 waits until completion. Diagnostics and type elaboration are advisory, not proof acceptance.");
  else {
    const timeout = Number(values["timeout-seconds"]);
    if (!values.workspace || !values.file?.length || !Number.isSafeInteger(timeout) || timeout < 0)
      throw new Error("--workspace, --file and a nonnegative --timeout-seconds are required");
    if ((values.type !== void 0 || values.context !== void 0) && (!values.type || !values.context || values.file.length !== 1))
      throw new Error("--type requires --context and exactly one --file");
    if (values.expression !== void 0 && !values.type) throw new Error("--expression requires --type and --context");
    const project = import_node_fs13.default.realpathSync(values.workspace);
    const constraints = import_node_path14.default.join(project, ".lake/source-constraints.json");
    if (import_node_fs13.default.existsSync(constraints)) assertSolverProjectSources(readMathJson(constraints), project);
    const controller = new AbortController();
    const abort = () => controller.abort();
    process.once("SIGINT", abort);
    process.once("SIGTERM", abort);
    let result2;
    const shared = {
      projectRoot: values.workspace,
      timeoutMs: timeout === 0 ? Infinity : timeout * 1e3,
      signal: controller.signal,
      onProgress: (file) => console.error(JSON.stringify({ event: "lean_check_started", file }))
    };
    try {
      result2 = values.type ? await checkLeanType({ ...shared, file: values.file[0], type: values.type, context: values.context, expression: values.expression }) : await runLeanDiagnostics({ ...shared, files: values.file });
    } finally {
      process.removeListener("SIGINT", abort);
      process.removeListener("SIGTERM", abort);
    }
    console.log(JSON.stringify(result2));
    process.exitCode = result2.timedOut ? 124 : result2.exitCode ?? 1;
  }
}
void main().catch((error) => {
  console.error(error instanceof SolverSourceError ? `${error.message}
File: ${error.proofPath}
${error.recovery}
Repair the saved file and rerun check-lean; no Lean compilation has started.` : error instanceof Error ? error.message : "math_diagnostics_failed");
  process.exitCode = 1;
});
/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*! Bundled license information:

smol-toml/dist/error.js:
smol-toml/dist/util.js:
smol-toml/dist/date.js:
smol-toml/dist/primitive.js:
smol-toml/dist/extract.js:
smol-toml/dist/struct.js:
smol-toml/dist/parse.js:
smol-toml/dist/stringify.js:
smol-toml/dist/index.js:
  (*!
   * Copyright (c) Squirrel Chat et al., All rights reserved.
   * SPDX-License-Identifier: BSD-3-Clause
   *
   * Redistribution and use in source and binary forms, with or without
   * modification, are permitted provided that the following conditions are met:
   *
   * 1. Redistributions of source code must retain the above copyright notice, this
   *    list of conditions and the following disclaimer.
   * 2. Redistributions in binary form must reproduce the above copyright notice,
   *    this list of conditions and the following disclaimer in the
   *    documentation and/or other materials provided with the distribution.
   * 3. Neither the name of the copyright holder nor the names of its contributors
   *    may be used to endorse or promote products derived from this software without
   *    specific prior written permission.
   *
   * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
   * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
   * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
   * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
   * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
   * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
   * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
   *)
*/
