# Snaky 复审证据提示与队列恢复

正常队列通知已于 `2026-10-24 13:45:11.603 UTC` 应用，edit 为 `READ-scratch-tmp-HOST-REVIEW-EVIDENCE-json`。原任务对象、已通过证明、canonical commit、planVersion 和当前 review assignment 全部保留；`affectedTasks=[]`，无需数学重验。见 `native-applied-readback.json`。

宿主先核对当前 review commit、sourceDigest、全部原目标的 receipt 绑定，再比较 reviewer 与 canonical 的所有 owned 源文件 SHA。真实全目标回执为 `lean-63766151ffe8a0523a860487`；只将原样记录的摘要及来源写到 reviewer 的 `.scratch/tmp/HOST-REVIEW-EVIDENCE.json`。该文件是辅助材料，不属于形式证明或 checkpoint，不授予验收权限。正常完整计划的通知名称提示其位置；本轮没有替 reviewer 写 verdict，也没有启动额外 Lean 编译。模型是否已经读取该文件尚无确认。

首次尝试新增 paused 参考任务时，我漏查旧读取器的限制：writer 允许 1 MiB，但此旧运行只按 64,000 字节读取一行。66,237 字节记录已入队但从未被消费，导致重复轮询错误。第一次压缩到 65,155 字节仍超过实际限制；这两次失败均保留原队列快照。随后在现有编辑写入锁内，仅撤回唯一尚未消费的尾行，保留全部已消费字节及其摘要。没有修改 state、已有回执、正式源码或 frozen runtime。

最终使用 `queue-evidence-notice.ts`：现有完整计划保持逐字相同，发送前实际检查 wire 小于 64,000 字节；证据放入允许的 scratch 目录，通过现有通知传递。原失败脚本 `queue-review-evidence.ts` 仅作历史记录，不应再次运行。撤回与通知应用的证据见 `unconsumed-rollback.json`、`notice-preparation.json`、`poll-recovery-observation.json`；通知应用后未再发现该轮询错误。

复审两次失败的独立调查见[超时定位](../snaky-review-timeout-inspection-20261024.json)：两次真实错误均为 SSE stream idle timeout，当前 60 秒。五项解题预算仍全部为 0；SSE 属于传输配置。可通过现有 `--codex` wrapper 为单次续跑覆盖，但需要重启并触发重新验核，本轮未因此中断当前复审，也未更改共享 profile。

复审、独立宿主最终检查和固定 publisher comparator 仍然有效。本包不表示 Snaky 原生最终通过。
