> Original Aristotle report accompanying Downloads/12. These are the producer's claims;
> local verification is recorded separately in M26-DELIVERY-12-MERGE.md.

# Summary of changes for run fac1baa7-4f9a-4111-9cfb-4c8ab4540d53
你说得对，上次交付的吸收并没有完成。这次我处理了你指出的两处缺口：DegreeRigidity 已经完整吸收；Logspace 的反向包含仍未完成，现在缺的只剩一条 `BPL ⊆ L`。

**DegreeRigidity：已吸收**
- 上游 975 个文件全部迁成 `Start/Rigidity<文件名>.lean`。做法和之前的目录一样：去掉 `OAI` 命名空间，每个文件加署名头。证明都沿用上游，只改了因版本不同而变化的名字：
  - 94 个文件做了 `ite_eq_left`/`ite_eq_right`、`dite_eq_left`/`dite_eq_right` 到 `if_pos`/`if_neg`、`dif_pos`/`dif_neg` 的脚本替换；
  - 2 个文件把 `Filter.eventuallyEqSet_iff` 改成 `Filter.eventuallyEq_set`；
  - 7 个文件把 `Measurable.of_eval` 改成 `measurable_pi_lambda`；
  - 1 个文件把归纳分支名 `ind` 改成 `h`。
  - 后三类共 10 个文件，各自在文件头里记录了改动。
- 主定理 `TuringRigidity.ManuscriptMain.rigidity` 已在本项目中编译通过，内容是：集合的图灵度上的每个序自同构都是恒等映射。
- 新增 `Start/RigidityBridge.lean`。它说明上游的 `Degree` 和本库原有的 `Lambda.Oracle.SetDegree` 是同一个商：`setDegreeOrderIso` 就是恒等映射。由此证明了任务板上的退出条件 `Lambda.Oracle.setDegreeRigidity : SetDegreeRigidity`。
- 主定理没有导入的唯一一个上游模块 `RigidityArithmeticRepresentation` 也已接到 `Start.lean`。所有新模块都已登记在 `Start/Capstones.lean`。
- 任务板上 `M26-OAI-DEGREE-RIGIDITY` 改为 DONE_STRONG。

**Logspace：反向包含仍未完成**
- 上游 Lean 里本来就没有 `RL ⊆ L` 或 `BPL ⊆ L` 的证明，所以这部分没有东西可以吸收。它是论文的主定理，论文正文约 7,900 行 LaTeX，用到 property (T) 混合、指纹比较、催化式对数空间控制器等。我没有把它形式化。
- 我新增的是 `Start/LogspaceAmplification.lean`，用的是上游自己的机器模型：
  - `RL_subset_BPL : RL ⊆ BPL`。构造是让两个副本在互不相交的工作带和输入头上交替运行，分别读取偶数位和奇数位的硬币，只要有一个接受就接受。已证明：若原机器在 \(T\) 步内停机，新机器在 \(2T\) 步内停机；接受概率是 \(1-(1-p)^2\)；所用空间不超过两个副本之和。
  - `RL_subset_L_of_BPL_subset_L` 和 `L_eq_RL_and_L_eq_BPL_of_BPL_subset_L`：只要再有 `BPL ⊆ L`，就能得到 `L = RL = BPL`。
- `M26-LOGSPACE-CONVERSE` 仍是 TODO_NEEDS_DESIGN，`M26-OAI-LOGSPACE` 仍是 DONE_WEAK，任务板上的说明已经更新。

**验证**
- `lake build Start` 成功（10507 个任务）。
- `check_sorry.py`（1788 个模块）、`check_closure.py`（1787 个模块）、`goal_state.py validate` 和 `pack_gate.sh HEAD` 都通过。
- 上述各个定理的 `#print axioms` 都只有 `propext`、`Classical.choice`、`Quot.sound`。

`NOTICE`、`README.md`、证据文件 `docs/goal/evidence/M26-OAI-ABSORPTION.md`（它原来"不值得吸收"的结论已标为作废）、`docs/current-goal-state.md` 都已更新。`NOTICE` 原本漏列的 DepthThree 也补上了。Properties 表里新增了几条：`RL ⊆ BPL`、条件等式、上游的 rigidity 和 `setDegreeRigidity`，状态都是 proved；`BPL ⊆ L` 单独一条，状态 in_progress。所有改动都已提交。

