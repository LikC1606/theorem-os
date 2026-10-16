# 恢复研究快照

`theorem-os recover` 从 `in-progress/<problem>` 恢复历史、完整冻结源码和 worker 草稿，再独立重检曾通过的辅助证明。整个过程不调用模型，也不改写原快照、manifest 或旧收据。

## 恢复源码

快照的 filtered fast-export 保留 `original-oid`，但导入后的 Git 提交 ID 会变化。部分临时校验投影未进入导出；快照也未包含 `config.json` 和 `holes.json`。缺失的冻结文件必须从对应官方版本取回，并与旧状态记录的 SHA-256 精确匹配。

先准备包含官方指定版本的 Git 对象库。它可以是 bare repository，无须检出保护的评测文件：

```sh
git init --bare /PATH/lean-eval.git
git -C /PATH/lean-eval.git fetch --depth=1 --filter=blob:none \
  https://github.com/leanprover/lean-eval.git \
  96a09300f9debeef864d8037635d6e0248c43960 \
  38361be884302c7edce1908c4aef8296eb2cb27e

bun bin/math.ts recover \
  --snapshot in-progress/dimitrov \
  --source-repo /PATH/lean-eval.git \
  --output /PATH/recovered/dimitrov
```

`--output` 必须尚不存在且位于快照目录之外。恢复命令只读取允许的公开文件，并检查 manifest 中全部文件的大小、SHA-256、路径及符号链接。不会读取 `Solution.lean`。

输出内容：

- `history/`：原始 filtered history 的独立 Git 对象库。
- `workspace/`：包含完整可信文件的 canonical 源码，重新验证原声明、上下文、目标与文件权限边界。
- `workers/<id>/`：各 worker 的源码、研究笔记和交付日志，包括尚未提交的捕获字节。
- `recovery.json`：旧提交到导入提交、重新物化提交的映射，缺失提交引用、候选任务和 worker 草稿的源码约束错误。
- `state.json`：独立的检查状态。原收据、线程、交付授权和整题验收结果不会被搬入此状态。
- `task.md`：SHA-256 与旧任务身份匹配的指令；Dimitrov 对应原 `task-continuation.md`。

原始 bootstrap 提交可能尚未包含主定理声明。因此新的源码仓库从满足原冻结约束的 canonical 版本建立基线；旧提交及其原字节仍保留在 `history/`。worker 草稿单独保存，不能替代 canonical 验收。

## 重新校验

准备匹配项目 `lean-toolchain` 和 `lake-manifest.json` 的工具链、包源码及编译缓存。Dimitrov 使用 Lean v4.33.0；Hopf–Rinow 和 Szemerédi 使用 v4.35.0-rc3。普通旧 Mathlib 缓存不能替代这些固定版本。

```sh
DEEPSCIENTIST_MATH_ENV_FILE=/PATH/new-runtime-env.json \
  bun bin/math.ts recover \
  --recheck /PATH/recovered/dimitrov \
  --packages /PATH/pinned-project/.lake/packages \
  --timeout-seconds 300

bun bin/math.ts inspect --run /PATH/recovered/dimitrov/state.json
```

运行环境可以通过现有 `.env` 或冻结 JSON 配置提供。使用新的配置文件；旧 JSON 绑定原主机绝对路径，会覆盖调用方的部分环境变量。校验器仍使用原来的沙箱、声明类型检查和可信依赖规则。

恢复会重查所有带历史通过记录的任务，包括已被旧取消错误标成 `blocked` 的任务。任务摘要按当前算法重新计算；不改写旧收据中的摘要、提交或 receipt ID。相同源码投影可合并校验，批量失败后逐项复查。每个新收据的源码提交和投影提交立即写入 `refs/math/<new-run-id>/evidence/`，防止对象失去引用。

退出码 `0` 表示候选辅助证明全部重新通过，`2` 表示仍有候选未通过，`1` 表示恢复或执行错误。取消后已完成的结果和未完成进度会保存；再次 `--recheck` 会重新核验全部候选。

## 证据与继续求解

恢复状态用于检查源码和读取新收据，不是可直接交给 `run --resume` 的旧运行。后续模型求解需要新的 bootstrap/run 和新线程，继续使用恢复的源码与研究记录；原有 `--resume` 身份检查保持严格。

辅助证明通过不代表主定理完成，也不代表官方 `lake test` / nanoda 验收通过。`recovery.json` 会登记无法精确找回的旧对象；新投影有自己的提交 ID 和收据，不能声称恢复了旧提交的相同哈希。

旧日志中的裸 `math_codex_rpc_failed:-32600` 缺少失败方法，无法由快照确定具体根因。恢复不复用缺失的模型会话。当前运行时已在新 RPC 错误中附带方法，并过滤不安全的错误码；没有对该错误增加无条件重试。
