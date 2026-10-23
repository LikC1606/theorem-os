# 验收可靠性修复验证记录

工程修复已在独立工作区完成并验证，当前运行的冻结 runtime 未替换。源码尚未提交或推送。

- 统一 host edit 写入和读取的 1 MiB UTF-8 行限制，按规范化 JSON 加最后换行计算；普通 worker delivery 仍为 64,000 字节。dry-run、正式入队、分段写入和恢复均已覆盖。
- 宿主检查与比较器的摘要保留首个 Lean 错误及上下文，附输出末尾，总摘要保持原字节上限。输出监听不接管 stdin 或进程生命周期，超时和沙箱后备行为保持。
- 宿主检查与模型预检使用 `-j1 -DElab.async=false`，参数绑定缓存身份。原冻结比较器命令及最终验收条件保持。
- 文档同步现有 scratch 保留行为，没有另外修改源码所有权规则。

验证：16 个去重测试文件、344 项测试通过；TypeScript 与 `git diff --check` 通过；三个无界面 bundle 构建通过。固定 Lean 4.34.1 在 32 GiB 地址空间、无超时下接受有效证明、拒绝错误证明。

完整路径、构建清单、每次测试计数、源码 SHA 和补丁 SHA 见 `validation.json`。`runtime-reliability-fixes.patch` 已通过当前工作树的反向 apply check，包含新增源文件和测试，不含依赖链接或其他工作区修改。

本记录只证明工程修复。数学题仍是 7 道完整原题模块化内核证明、4 道原生最终通过；本轮没有新增最终通过，也没有 OpenAI 托管接受证据。数学候选修复包含外部辅助，新的候选仍须通过原源码保护、完整内核、独立比较器和原生最终验收。

CharacterVarieties 的外部续接脚本也已修复：使用标准库 xz/lzma + base64，并从 `COOPERATION.json` 对应 task 的完整 objective 回读载荷，避免模型提示截断。每次实际入队前，按当前候选重新编码，并检查规范化 edit 加末尾 LF 不超过旧冻结 reader 的 64,000 字节；原有同 SHA 内核、源码保护和比较器门禁保留。

只使用已知有 Lean 错误的 V3 文件作为传输测试夹具（729,113 字节，未递送）。完整消息 44,674 字节；旧冻结 reader 已实际消费测试行，bubblewrap 沙箱内 Python 解压得到完全相同 SHA，损坏 objective digest 会在写入前拒绝，中文、引号、反斜线和换行回环均通过。新候选仍须重新测量且通过数学检查；这项结果没有新增数学或原生通过。脚本差异见 `character-continuation-transport.patch`，详细回执见 `validation.json` 中 continuationTransportFix。

新完整 V4 候选生成并通过原源码保护后，也已复测传输：751,283 字节，SHA256 `6c6aa7b347160883265dd210c22609a3cc148b031113c7d1a0b936cd63678341`；规范化编辑行 45,182 字节，旧 reader 与沙箱解压回环均通过。完整候选内核、比较器及原生验收仍待后续检查，未入队。真实新候选回执是 `character-source-transport-roundtrip-v4-candidate.json`。
