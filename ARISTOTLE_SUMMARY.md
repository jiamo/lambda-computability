# Summary of changes for run 97a377e0-71b5-4122-bf5d-4370ca1912c8
I picked the project up where it stood, made the delivered tree buildable again, and closed out the line of work that had been left dangling — the `PSPACE`-hardness of `TQBF` — then pushed it one step further. Everything is committed; `lake build` succeeds (9180 jobs, no errors), the library contains no `sorry`/`admit`, and every repository gate passes.

**1. The delivered tree could not be built.** `lake-manifest.json` again disagreed with `lakefile.toml` (wrong package name, wrong Mathlib input revision, `cslib` missing), so a clean clone refused to build. I repaired the manifest, resolved and fetched the dependencies for the pinned pair (Lean v4.33.0, Mathlib `v4.33.0`, the pinned `cslib`) and rebuilt the whole tree. `scripts/check_manifest.py`, `scripts/check_sorry.py` (462 modules), `scripts/check_closure.py` (461 modules), `scripts/goal_state.py validate` (223 tasks) and `scripts/pack_gate.sh` on what `git archive` actually ships all pass.

**2. Eleven finished modules were outside the library and are now in it.** `Start/CobhamCond.lean`, `Start/CobhamUnary.lean`, `Start/CobhamFieldsApp.lean`, `Start/QbfMachineDepth.lean` and the `Start/QbfCob{Cfg,StepCase,Step,InitAcc,Levels,Machine,Reduction}.lean` chain were present but imported by nothing, so they were neither built nor gated. They are now in the import closure, registered with prose and `#check`s in `Start/Capstones.lean`, and covered by the gates. Their content is the polynomial-time compiler of the reduction: unary comparison and bit-reading, parameter words carrying a word, the reduction formula at an arbitrary recursion depth, the configuration blocks, the guarded cases of the step formula, the initial and accepting constraints, the sweep over the levels, and their concatenation — culminating in `Complexity.Qbf.QBF.pspaceHard_tqbfLang` and `.npspaceHard_tqbfLang`: **every language of (nondeterministic) polynomial space reduces to `TQBF` by one Cobham term of the input**, i.e. in polynomial time. `#print axioms` on these reports only `propext`, `Classical.choice`, `Quot.sound`.

**3. New: hardness as a property, and what it buys (`Start/QbfHard.lean`).** `Complexity.Space.PSPACEHard`, `.NPSPACEHard` and `.PSPACEComplete` are now predicates of a language; hardness travels along reductions (`PSPACEHard.of_reduction`), `TQBF` is hard in that vocabulary (`pspaceHard_tqbfLang'`), and a hard language decided in polynomial time decides the whole class — `pspace_inP_of_tqbf_inP`, with the contrapositive `tqbf_not_inP` and the `NP` analogue.

**4. New: the evaluator's memory in the length of the code (`Start/QbfCodeSpace.lean`).** A `PSPACE` membership is a statement about codes, so the size, variable bound and height of a formula are compared with the length of its binary code (`size_le_length_enc`, `varBound_le_length_enc`, `height_lt_length_enc`), giving `tqbf_memBits_le_length_enc`: deciding a closed formula costs at most `2n² + 3n` bits, `n` the length of its code.

**Honest boundary, recorded in the modules, the evidence notes and the task board.** `TQBF` is proved hard but not *complete*: the membership `TQBF ∈ PSPACE` would need the evaluating stack machine compiled into the offline machine of `Start/SpaceMachine.lean`, respecting exactly the bound proved in item 4; that is the remaining task `M14-TQBF-IN-PSPACE`, whose boundary is now narrowed to that compilation. The other open research items (the Krivine space bound against `DSPACE`, the converse space simulation, the priority constructions, the effective-topos programme, the metacomplexity and open-problem milestones) remain recorded with their exit criteria.

**Bookkeeping.** Six task-board entries moved to `DONE_STRONG`, `M14-TQBF-PSPACE-HARD` to `DONE_WEAK` with hardness proved and completeness pending, two new tasks were added for the new modules, two evidence notes were written, `docs/current-goal-state.md` was re-rendered and `README.md` updated. `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 4dc9812d-5228-4b99-817c-793ad881276c
I picked the project up, made the delivered tree buildable again, and pushed two of the open research items forward with new, machine-checked mathematics. Everything is committed; the whole library builds, contains no `sorry`/`admit`, and all of the repository's own gates pass.

**1. The delivered tree could not be built.** `lake-manifest.json` again disagreed with `lakefile.toml` (wrong package name, mathlib recorded at the wrong input revision, `cslib` missing), so a clean clone refused to build; on top of that the dependencies had to be resolved for the pinned pair Lean v4.33.0 / Mathlib `v4.33.0` before anything compiled. I repaired the manifest, resolved and fetched the dependencies, and rebuilt the whole tree: `lake build` succeeds (9168 jobs) with no errors, `scripts/check_manifest.py`, `scripts/check_sorry.py` (449 modules), `scripts/check_closure.py` (448 modules, all in the import closure and all registered), `scripts/goal_state.py validate` (212 tasks) and `scripts/pack_gate.sh` on the packed tree all pass.

**2. New: time-bounded Kolmogorov complexity `K^T` (`Start/KolmogorovTime.lean`).** `K^T(s)` is the least size of a closed term reducing to the numeral of `s` in at most `T` beta steps, built as an instance of the library's description systems, so that it sits beside plain `K`, prefix complexity and Levin's `Kt`. Proved: the minimum is attained and `K^T(s) ≤ k` is equivalent to the existence of a bounded certificate (`ktime_le_iff`); `K^T` decreases in `T` (`ktime_antitone`); `K ≤ K^T ≤ 3s+3` (`kolm_le_ktime`, `ktime_le_church`); for every `s` the two measures agree from some bound on (`exists_bound_ktime_eq_kolm`, `ktime_eq_kolm_of_le`); the counting bound and incompressibility are inherited (`finite_setOf_ktime_le`, `exists_incompressible_ktime`); the comparison with Levin's measure (`kt_le_ktime_add_log`, `ktime_le_of_kt`); and **invariance** — a change of interpreter costs at most an additive constant and no extra time (`ktime_le_ktimeWith`), the identity interpreter costing one extra step (`ktimeWith_I_le_ktime`). Honest boundary, recorded in the module, the evidence note and the task board: the remaining exit criterion — that `{(x, k) : K^T(x) ≤ k}` is in `NP` in the library's time model — is *not* proved; `ktime_le_iff` supplies its combinatorial half, the missing half being that running a guessed term for `T` steps is polynomial-time checkable.

**3. New: the order of partial combinatory algebras under applicative morphisms (`Start/PCAOrder.lean`).** Ordering algebras by the existence of a morphism is a preorder (`PCALe`, `pcaLe_refl`, `pcaLe_trans`) with its induced equivalence, but it is **degenerate**: the trivial morphism makes any two algebras equivalent (`pcaEquiv_of_any`), so it separates nothing. The informative order is carried by the morphisms that *decide* their representatives — one element of the target tells representatives of `k` from representatives of `k i` (`AppMorphism.Decides`); the identity decides and decidable morphisms compose (`decides_id`, `decides_step`, `Decides.comp`), giving a preorder `PCALeD`. In it the two Kleene algebras are separated: the morphism `K₁ → K₂` decides (`kOneToTwo_decides`), while a decision of the two combinators would already separate bits, which no morphism `K₂ → K₁` can do (`separatesBits_of_decides`, `not_decides`) — hence `kleene_strict : K₁ < K₂`. The third exit criterion of that task (algebras with equivalent realizability toposes) is recorded as open, since the library has the assemblies and their exact completion but not the realizability topos itself.

**4. Housekeeping.** Both new modules are imported by the root module and registered with prose and `#check`s in `Start/Capstones.lean`; `README.md` gained descriptions of both; two evidence notes were written (`docs/goal/evidence/M19-KT-DEFINITIONS.md`, `docs/goal/evidence/M18-PCA-LATTICE.md`), the corresponding task-board entries moved from open to `DONE_WEAK` with explicit boundaries, and `docs/current-goal-state.md` was re-rendered. One deprecation warning was fixed at its root in `Start/OracleUse.lean`. `#print axioms` on every new headline result reports only `propext`, `Classical.choice`, `Quot.sound`. The seven remaining build warnings are the pre-existing universe-linter false positives already documented in the category-theory modules. `ARISTOTLE_SUMMARY.md` was left untouched.

**What is still open.** The research queue is not exhausted: `TQBF` is still not proved `PSPACE`-hard (the missing half is the polynomial-time compiler that writes the reduction formula), the Krivine space bound against `DSPACE` and the converse space simulation are untouched, and the remaining items of the queue — Friedberg–Muchnik and the priority constructions, the effective-topos programme, Kreisel–Lacombe–Shoenfield and the Weihrauch degrees, MCSP and the metacomplexity items, and the open-problem milestone — remain recorded with their exit criteria on the task board.

# Summary of changes for run 54fd5327-aa59-41ce-a838-0173d92d6cdf
I picked up the project where the previous work left off, repaired the delivery, and pushed the one genuinely open line of work — the `PSPACE`-hardness of `TQBF` — several concrete steps further. Everything is committed; the whole tree builds with no `sorry`/`admit` and all repository gates pass.

**1. The delivered tree could not be built.** `lake-manifest.json` again disagreed with `lakefile.toml` (wrong package name, wrong Mathlib `inputRev`, missing `cslib`), so a clean clone refused to build. I resolved the dependencies against `lakefile.toml`/`lean-toolchain` (Lean v4.33.0, Mathlib `v4.33.0`, the pinned `cslib`), rebuilt the whole library (9157 jobs, 0 errors), and `scripts/check_manifest.py` and `scripts/pack_gate.sh` now pass on what `git archive` actually ships.

**2. An orphaned module was brought back into the library.** `Start/QbfWord.lean` — the binary code of quantified Boolean formulas, its decoder and injectivity, and the reduction of every `PSPACE` (indeed `NPSPACE`) language into the language `Complexity.Qbf.tqbfLang` by a map of *words* of polynomially bounded output length — existed but was not imported by `Start.lean`, so it was neither built nor gated. It is now in the import closure, registered in `Start/Capstones.lean`, and covered by the gates.

**3. New: the code of the reduction formula as a stream of blocks** (`Start/QbfWordStream.lean`). Quantifier prefixes are concatenations over a range, finite conjunctions and disjunctions concatenations over their case lists, and — the key point, because the midpoint recursion has a single recursive call — the reachability formula's code is exactly one block per level, with the parameters of level `j` in closed form (`enc_reachF`, `enc_machineF_stream`). This is the uniformity shape a polynomial-time compiler needs.

**4. New: the first pieces of that code are now *computed*, not just described** (`Start/CobhamRange.lean`, `Start/CobhamFields.lean`, `Start/QbfCobPrefix.lean`, `Start/QbfCobEqBlock.lean`, `Start/QbfCobLevel.lean`). Writing one block per index of a range is a polynomial-time (Cobham) function (`eval_rangeEmitTerm`, resting on truncated subtraction of unary words, `Cob.eval_dropN`); a parameter word of unary fields is readable by Cobham terms (`Cob.eval_fieldTerm`); and single Cobham terms write the quantifier prefixes (`eval_quantPrefixTerm`), the block-equality formulas (`enc_eqBlock_eval`) and the whole block that one level of the midpoint recursion contributes (`reachPre_eval`). The padding constants of these terms do not depend on the instance, so one term serves every width, offset, block index and level — which is what a uniform reduction requires.

**Honest boundary, recorded in the module docs, the task board and the evidence files.** `TQBF` is still not proved `PSPACE`-hard: what remains is the sweep over the levels (which must build each level's parameter word from the counter) and the machine's own constraints (`stepF`, `initF`, `accF`), followed by the final assembly. The two other open items (the Krivine space bound stated against `DSPACE`, and the converse simulation) were not started this session and remain recorded as open.

**Bookkeeping.** Five new modules are imported by `Start.lean` and registered with prose and `#check`s in `Start/Capstones.lean`; the task board gained three `DONE_STRONG` tasks with evidence files (`M14-QBF-WORD-LANG`, `M14-QBF-WORD-STREAM`, `M14-QBF-COB-PIECES`), the open `M14-TQBF-PSPACE-HARD` boundary was narrowed accordingly, `docs/current-goal-state.md` was re-rendered (183 tasks), and the README library map was updated. Gates: `lake build` succeeds with no new warnings, `check_sorry.py` reports no `sorry`/`admit` in 438 modules, `check_closure.py`, `goal_state.py validate`, `check_manifest.py` and `pack_gate.sh` all pass, and the new results depend only on the standard axioms.

# Summary of changes for run 49464b6b-5b25-47f7-8422-3d1ca1e1adf8
本轮把之前一直空着的那条线——空间复杂度——补上了，并顺手修好了交付树本身编不了的问题。所有改动已提交。

**0. 先修通道。** 交付的 `lake-manifest.json` 又是坏的（包名不对、缺 `cslib`、mathlib 的 `inputRev` 与 `lakefile.toml` 不符），干净克隆里 `lake` 直接拒绝构建。已按 `lakefile.toml` 与 `lean-toolchain` 重新解析依赖（Lean v4.33.0 + mathlib `v4.33.0` + 锁定的 `cslib`），`scripts/check_manifest.py` 通过，全树 `lake build` 成功（9141 jobs，0 error、0 linter warning）。

**1. 空间受限计算的机器模型（`Start/SpaceMachine.lean`）。** 只读输入带（读头被夹在输入与结束标记之间）＋一条二进制工作带的离线图灵机；转移函数返回「可选指令的列表」，于是确定性只是同一模型上的一条性质。在其上定义 `DSPACE`、`NSPACE`、`LOGSPACE`、`PSPACE`、`NPSPACE`（多项式界沿用库里时间那半边的 `Complexity.PolyBound`），证明了 `DSPACE ⊆ NSPACE`、`PSPACE ⊆ NPSPACE`、`L ⊆ PSPACE`、对界的单调性，以及一台见证类非空的机器。

**2. 构形计数（`Start/SpaceConfigCount.lean`）。** 空间为 `s`、输入长 `n` 时构形至多 `q·(n+1)·(s+1)²·2^s` 个；机器的运行恰是这张有限图上的走道，接受即「可达某个接受构形」，因而接受运行总可以缩短到构形数以内。

**3. 可达性与中点递归（`Start/SavitchReach.lean`）。** 走道的合成与分解、中点恒等式（`2^(k+1)` 步可达 ⟺ 存在中点两腿各 `2^k` 步）、有限图中走道可缩短到顶点数以下（鸽笼＋去圈），以及「深度 `k` 的中点递归判定可达性」。

**4. 真正执行递归的机器（`Start/SavitchVM.lean`）。** Savitch 定理的内容是「这个递归能在小内存里跑」，所以给出实现：一台确定性栈机，活动记录只存两个顶点、深度、一个指向顶点枚举的**下标**和一个比特（枚举本身不进内存）。一次归纳同时证出正确性与栈高界——从深度 `k` 的子问题出发返回递归的值，且**沿途每个状态**的活动记录不超过 `k` 条，于是内存 `(k+1)·(2w+2d+1)` 比特。

**5. Savitch 定理（`Start/SavitchSpace.lean`）。** 把栈机实例化到构形图：判定过程正确（`savitch_accepts_iff`），每次可达性询问由栈机在 `(k+1)·(4k+3)` 比特内完成，且 `k ≤ log₂q + log₂(n+1) + 2log₂(s+1) + s`，即 `O((s+log n)²)`；对 `NPSPACE` 中的语言，模拟所用内存被输入长度的多项式界住（`savitch_poly_memory`）。

**6. 量化布尔公式（`Start/Qbf.lean`）。** QBF 的语法与语义、闭公式的值与赋值无关（故 `TQBF` 良定义），以及求值栈机：返回公式的值、归还它拿到的赋值（每个量词恢复被覆盖的那一位）、活动记录不超过公式高度，于是判定闭公式的内存关于公式规模是二次的——TQBF 属于多项式空间那一半。

**诚实边界（已写进模块文档、证据文件与任务板注释）：** 确定性模拟是在栈机上给出的，内存按活动记录的比特计数；把栈机再编译回离线图灵机模型（那是空间的模型无关性中例行、繁琐的一半）没有形式化，因此**没有**把 `NPSPACE = PSPACE` 当作关于 `DSPACE` 的定理来断言；TQBF 的 PSPACE-难（从空间受限机器到公式的通用归约）同样没有做。

**记账与验证。** 五个新模块被 `Start.lean` 导入、在 `Start/Capstones.lean` 里带散文与 `#check` 注册；README 增补了「空间复杂度与 Savitch 定理」一节和库地图条目；任务板新增里程碑 M13（六条任务，全部 DONE_STRONG）并配六份证据文件，`docs/current-goal-state.md` 重新渲染（172 条任务）。全树 `lake build` 成功、零警告，`Start/` 下无 `sorry`/`admit`（422 个模块），新结论 `#print axioms` 只有 `propext`、`Classical.choice`、`Quot.sound`，`goal_state.py validate`、`check_closure.py`、`check_sorry.py`、`check_manifest.py` 与打包门 `scripts/pack_gate.sh` 全部通过。

# Summary of changes for run fe076533-53d1-498e-870d-ebf0f38cf033
**0. 通道先修（你说的最后一步，已在本克隆里执行）**
- 在这个仓库里跑了一次 `scripts/install_hooks.sh`：`core.hooksPath = .githooks` 现已生效，并实测验证——本次每一次正式提交都触发了 `pre-commit`，它在**暂存树**上跑 `scripts/pack_gate.sh`，四道门（manifest / sorry / task board / import 闭包）全部打印通过。
- `lake-manifest.json` 交付时又是坏的（包名 `start`、mathlib 的 `inputRev` 停在 `v4.28.0`、没有 `cslib`），因此整棵树在干净克隆里编不了。已按 `lakefile.toml` 与 `lean-toolchain` 重新解析：Lean v4.33.0、mathlib `v4.33.0`（`db584cd6…`）加匹配的 batteries/aesop/Qq/proofwidgets/Cli/plausible/importGraph/LeanSearchClient，以及锁定的 `cslib`；`python3 scripts/check_manifest.py` 现在 exit 0，全树可编。

**1. Eff 那条：把“被自己证否的那半”补上（你排的第一位）**
新增两个模块，全部 sorry-free：
- `Start/AsmExRegProj.lean`：完备化中底对象为 **partitioned assembly**（即 `Asm(A)` 的正则投射，`Assembly.regularProjective_iff`）的对象构成的全子范畴 `Realizability.ExReg.ExRegP`；以及做这件事的关键工具——**探针**（`pairERel`，点就是自己的实现子，故底对象天然 partitioned，`partitioned_pairERel`、`homotopic_pair`）。用探针把“联合单”读成算法内容：一个元素即可从两点的实现子与“两条腿的像相关”的证明造出“两点相关”的证明（`JMTracker`、`jmTracker_of_jointlyMono`）；另一枚探针把**可复合对**也变成投射对象（`compData`），于是商的传递性只需要投射对象上的复合，这正是子范畴所能提供的（`EqvDataP`、`eqvDataP_of_isInternalEquiv`）。
- `Start/AsmExRegEffective.lean`：把 `Start/AsmExRegCoeq.lean` 的商在这套较弱数据上重建（`coeqObjP`、`coeqPreP`、`coeqCoforkPIsColimit`），并证出关键的**提升**：底对象 partitioned 的对象上，两个在商里同伦的映射一定经过关系分解，且分解唯一（`exists_liftPre`、`existsUnique_lift`）——点只有唯一实现子，于是“选哪个点 + 算它的实现子”这一步变成函数，而这恰是反例在任意底对象上封死的一步。结论：**`ExRegP` 上每个内部等价关系都是有效的**——商映射是它们的余等化子，它们是该映射的核对（`ExRegP.exists_effective_quotient`、`ExRegP.isKernelPair_of_isInternalEquiv`）。另有非空性与定位引理：`ExRegP.regularProjective_base`、`embP`、`isInternalEquiv_id`。
- 记账：新模块被 `Start.lean` 导入、在 `Start/Capstones.lean` 里带散文与 `#check` 注册；`README.md` 增补一节；任务板新增 `M12-EXREG-PROJ-EXACT`（DONE_STRONG）并配 `docs/goal/evidence/M12-EXREG-PROJ-EXACT.md`，`M12-EFF-EXREG` 的证据文件改写（把“Not done”列表按新进展更新），`docs/current-goal-state.md` 重渲染（166 条任务）。

**诚实边界（未做，已写进模块文档、证据文件与任务板）**：受限子范畴自身作为范畴的正则性（有限极限与像分解只在同构意义下留在子范畴内，因为 `Start/AsmExRegEq.lean` 的等化子把见证放进了实现子）、完备化在正合范畴中的普遍性质、topos 结构（子对象分类子与指数）、以及与 effective topos 的认同。你列的第 2 条（空间复杂度类 DSPACE/PSPACE/L、Savitch、TQBF 的 PSPACE-完全性）本次**没有**动——库里仍然只有 `InP`/`InNP`/`NPComplete`，那条线保持原状。

**验证**：`lake build` 全树成功（9135 jobs，0 error、0 linter warning），`Start/Demo.lean` 也编过；`Start/` 下无 `sorry`/`admit`（`check_sorry.py`：416 个模块）；新结论 `#print axioms` 只有 `propext`、`Classical.choice`、`Quot.sound`；`goal_state.py validate`、`check_closure.py`（415 模块全在导入闭包且全部注册）、`check_manifest.py`、`pack_gate.sh` 全部通过。所有改动已提交。

# Summary of changes for run 9670534a-dcaf-41f2-9d9c-ca69dedf63c3
All outstanding work on the project is now finished; the whole library builds clean under the pinned toolchain.

**The open question — exactness of the exact completion of the assemblies — is settled, in both directions.**

1. *Not exact* (`Start/AsmExRegNotExact.lean`, new). The completion `ExReg(A)` carries an internal equivalence relation that is the kernel pair of no morphism, over any partial combinatory algebra with three distinct elements, and in particular over Kleene's first algebra (`Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair`, `.kleene_exReg_not_exact`). The notion used is the standard one: `.IsInternalEquiv` (jointly monic, with a diagonal, a swap and composites), and every kernel pair satisfies it (`.isInternalEquiv_of_isKernelPair`). The obstruction is uniformity — a morphism must pick one point per point of the source *and* compute a realizer of the chosen point from a realizer of the source point — and the counterexample attaches to each element of the algebra a pair of witnesses that this element itself cannot normalize, which is possible by a three-point pigeonhole since application is single-valued.

2. *But it does have the quotients* (`Start/AsmExRegCoeq.lean`, completed). Every internal equivalence relation of the completion has a coequalizer (`Realizability.ExReg.Coeq.hasCoequalizer_of_isInternalEquiv`, with the colimit `.coeqCoforkIsColimit`): the base of the object with the relation generated by the two legs, its transitivity read off a newly built object of composable pairs. This module previously contained only a few combinators and was not part of the library; it is now finished and wired in.

So the completion of *all* assemblies is regular but not exact, which also explains why the effective topos is obtained by restricting the bases to the regular projectives.

Both new modules are imported from the root module and registered in `Start/Capstones.lean`, whose prose was extended accordingly; `README.md` gained a section on the exact completion, and the two evidence files `docs/goal/evidence/M12-EXREG-REGULAR.md` and `docs/goal/evidence/M12-EFF-EXREG.md` were rewritten. In `docs/goal/task-board.yaml` the two remaining `DONE_WEAK` items (`M12-EXREG-REGULAR`, `M12-EFF-EXREG`) are now `DONE_STRONG` with empty open boundaries; the original exactness exit criterion is preserved verbatim in a comment next to the corrected one, since it turned out to be false as stated. All 165 tasks are now `DONE_STRONG`, and `docs/current-goal-state.md` was re-rendered.

Verification: `lake build` completes successfully for the whole project (414 modules, plus `Start/Demo.lean`) with zero errors and zero warnings; there is no `sorry` or `admit` anywhere; the headline theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. All offline gates pass, including `scripts/pack_gate.sh` on the packed tree (manifest, sorry, task board, import closure) and the goal-state unit tests. `lake-manifest.json` was repaired: it now records the genuine `v4.33.0` dependency revisions (mathlib `db584cd6…` and the matching batteries/aesop/Qq/proofwidgets/Cli/etc.) together with the pinned `cslib`, so it agrees with `lakefile.toml`, `lean-toolchain` and the README. Two small elaboration/linter fixes were made in the counterexample module so that it is warning-free on the pinned toolchain, and an ad-hoc single-file checking script left over from earlier work was removed in favour of the project's own `scripts/check_file.sh`.

# Summary of changes for run fdd436a0-535a-4e45-8173-bed640726b95
I picked the project up where it stood and closed the remaining open items on its task board. The whole tree builds green (9118 jobs, zero errors and zero linter warnings), `Start/` contains no `sorry`/`admit`, and all the project's own gates pass (`goal_state.py validate` — 159 tasks, `check_closure.py` — 398 modules, `check_sorry.py` — 399 modules, `check_manifest.py`, `pack_gate.sh`). Everything is committed.

**Dependency manifest repaired.** The checked-in `lake-manifest.json` disagreed with `lakefile.toml` (wrong package name, missing `cslib`, stale mathlib revision), so the tree could not be built at all. It is regenerated and now resolves mathlib v4.33.0 and cslib; `scripts/check_manifest.py` passes.

**One Krivine transition on a machine model (task M11-KRIVINE-PASS-MACHINE, previously open).** The mathematics in `Start/KrivineCobWord.lean` and `Start/KrivineCobStep.lean` was present but unregistered and unrecorded. I verified it, registered it in `Start/Capstones.lean` (prose plus `#check`s), and closed the task: `Krivine.Impl.stepT` is a single Cobham term that turns the encoding of a valid machine state into the encoding of its successor (`Krivine.Impl.eval_stepT`, the empty word meaning a stuck machine), its cost in that model is polynomial in the length of its input (`Krivine.Impl.stepT_compiles`), and `Krivine.Impl.eval_impl_cob_cost` composes this with the transition count. This empties the open boundary of `M11-KRIVINE-UNIT-COST` and of `M11-KRIVINE-INVARIANCE`, both now recorded as fully done.

**New mathematics: when a full model is equivalent to the strictification of its contexts (task M10-CWA-DEMOCRATIC, previously weak).** Its last exit criterion asked for an equivalence, in the lax 2-category of models, between a full democratic model and the strictification of its category of contexts. I settled it, in the negative, with two new modules.

- `Start/CwaStrictifyEquiv.lean`: in the lax 2-category an isomorphism of 1-cells is exactly an isomorphism of the functors on contexts (`Cwa.laxIsoOfNatIso`), so the only thing an equivalence needs beyond the existing comparison `Cwa.fullStrictify` is a morphism of models back that is the identity on contexts (`Cwa.fullStrictify_comp_iso_id`, `Cwa.comp_fullStrictify_iso_id`) — i.e. a universe naming every type.
- `Start/CwaFamiliesNoStrictify.lean`: the standard model of families (contexts are types, a type over Γ is a family `Γ → Type u`) is full, democratic and coherent (`CwaType.isFull_families`, `CwaType.isDemocratic_families`, `CwaType.extCoherent_families`) and has no such universe. Substitution acts on the classifying map alone, so the generic family assigned to a type is substitution-invariant (`CwaType.total_tySub`); a family over a two-element context connects any two closed types, so all closed types share one generic family (`CwaType.total_const_eq`); each closed type embeds into it (`CwaType.exists_injective_total`); Cantor's theorem then forbids the whole thing (`CwaType.false_of_mor_isEquivalence`). Hence `CwaType.not_equivalent_ofPullbacks`: the standard model is **not** equivalent, in the lax 2-category, to the strictification of its own category of contexts.

`#print axioms` on every headline result above reports only `propext`, `Classical.choice`, `Quot.sound`.

**Bookkeeping.** The task board and `docs/current-goal-state.md` were updated and re-rendered (158 of 159 tasks now `DONE_STRONG`; the single remaining `M9-LAMBDAPI-LCCC` keeps an explicit, honest boundary and is no longer blocked by anything I could close with new proofs), a new evidence note was written for the pass-machine task, three existing evidence notes were rewritten to match their new status, and `README.md` now describes both new developments.

# Summary of changes for run ecfe8d64-3edf-4a52-b36f-3dce34bbacfb
已按顺序做完你列的三件事，全部在本仓库里落地并提交。

**0. 通道与门禁（先修）**
- `lake-manifest.json` 与 `lakefile.toml` 确实是断的：manifest 里没有 `cslib`、包名写成 `start`、mathlib 的 `inputRev` 还停在旧标签，所以整棵树根本编不了。已重新生成，`python3 scripts/check_manifest.py` 现在 exit 0；`lake build` 全绿（9111 jobs，0 error、0 linter warning），`Start/` 无 `sorry`/`admit`。
- `Start/ArithBounded.lean` 里的 `push Not`：在本仓库锁定的 Mathlib 版本上，情况正好相反——`push_neg` 已被弃用，官方提示改用 `push Not`。我实测把两处改成 `push_neg` 会产生两条 deprecation warning，于是保留原样，并在此说明。

**1. 合理时间代价模型（①②③，三个新模块，全部 sorry-free，公理只有 `propext`/`Classical.choice`/`Quot.sound`）**
- ① `Start/Krivine.lean`：抽象机（闭包／环境／栈），三条带标号的转移（`app`/`beta`/`var`），`Run n b` 同时计总步数与 β 步数，并通过 `Krivine.Run.starN` 接到已有的计步重写接口；确定性、终止态刻画、环境的结构深度（`var` 转移严格下降）。
- ② `Start/KrivineDecode.lean`：状态解码（环境按并行代换展开、栈还原成应用脊），双向模拟——`Trans.decode_eq`（管理转移不改变项）、`Trans.decode_wstep`（一次 `beta` 恰是一次弱头 β 步）、`Run.decode_reducesIn`（b 次 β 转移 = 恰好 b 步 β 归约）、终止态解码为弱头范式，以及反方向的 `exists_final_of_whnIn`（项弱头可归约 ⇒ 机器一定停机，且 β 转移数 ≤ 策略步数）。
- ③ `Start/KrivineBound.lean`：子项不变量（代码大小不增）+ 深度不变量（只有 β 转移会加深、且只加深 1）+ 势函数（`|code| + S·envDepth`，每个管理转移严格下降），得到 `run_length_le_init`：从 `t` 出发、含 b 次 β 转移的运行总步数 `n ≤ b + |t|·(1 + b·(b+1))`；与 `Run.beta_le`（`b ≤ n`）合起来即两种代价多项式相关。总结论 `Krivine.eval_cost`。文件末尾有 `(λx.x)(λx.x)` 的实例（3 步、1 次 β）作为非空性检查。
  - 诚实边界：这里界的是**转移条数**，"单步开销在具体机器模型上多项式有界"那一半没有形式化（库里的机器模型尚未与 Krivine 机对接），所以该任务记为 `DONE_WEAK`，并单独立了一条待办 `M11-KRIVINE-UNIT-COST` 写清了 exit criteria。

**2. K₁ ↪ K₂ 不可逆（`Start/KleeneNoRetraction.lean`）**
你给的原命题（"不存在 K₂→K₁ 的 applicative morphism"）按本库的定义是**假**的：我构造了任意两个 PCA 之间的平凡态射 `AppMorphism.trivialMor`（目标的每个元素代表源的每个元素，实现子取常函数），这本身就是反例，已写进文件并在文档里说明。修正后的命题已证：`KleeneTwo.no_separatesBits_morphism`——任何 K₂→K₁ 的 applicative morphism 都无法用一个部分递归码把常函数 0 的代表与常函数 1 的代表分开（更强的"读回全部数码"版本是 `no_readsNumerals_morphism`、`kOneToTwo_not_invertible`）。证明用投影 `β ↦ β n` 的连续性（它们是 K₂ 的元素 `projAssoc n`）：能分辨一位，就能从一个代表恢复整条 0/1 序列，于是自然数集会被自然数命名，与 Cantor 定理矛盾。

**3. 记账**
四条任务（`M11-KRIVINE-MACHINE`、`M11-KRIVINE-SIMULATION`、`M11-KRIVINE-INVARIANCE`、`M11-KLEENE-NO-RETRACTION`）已按 board 的 schema（exit_criteria + required_gates + depends_on + rank + terminal_statement）写进 `docs/goal/task-board.yaml`，每条配了 `docs/goal/evidence/` 下的证据说明；`docs/current-goal-state.md` 已重渲染，新模块都被 `Start.lean` 导入、在 `Start/Capstones.lean` 里带散文与 `#check` 注册，README 也更新了。三个项目自带门禁全部通过：`goal_state.py validate`（158 tasks）、`check_closure.py`（391 modules 全在导入闭包且全部注册）、`check_manifest.py`。所有改动已提交。

# Summary of changes for run 6b45f683-785b-4418-a8a1-29c2be412515
I picked the project up, repaired the build, and closed the main item that was still open on its research queue. Everything is committed and pushed.

**1. The repository builds again.** The checked-in dependency manifest disagreed with `lakefile.toml`, so nothing compiled ("dependency 'cslib' not in manifest"); it is regenerated against Lean v4.33.0 / Mathlib `v4.33.0` with matching revisions of every transitive dependency and of `cslib`. One genuine proof error also surfaced (`Start/MultiTypes.lean` gave a size-`1` witness for a derivation of size `0`); it is fixed. `lake build` now compiles the whole library — 9107 jobs, 387 modules — with no error and no linter warning, and there is no `sorry` or `admit` anywhere under `Start/`.

**2. The contexts of a full model with dependent products are locally cartesian closed** (new modules `Start/CwaHomOver.lean`, `Start/CwaLcccOfFull.lean`). The library already had this for *strictified* models, where a type is a local universe and a term is presented by its code; the general case needed different machinery.
- `Cwa.HomOver`, `Cwa.homOverEquivTm` — in an arbitrary category with attributes, the maps into a display map lying over a substitution are exactly the terms of the substituted type, and precomposing the map of a term is substituting the term (`Cwa.homOverEquivTm_symm_precomp`, `Cwa.tmCast_tmSub_extend`).
- `Cwa.LcccOfFull.piObj`, `Cwa.LcccOfFull.transpose` — the candidate dependent product of a slice object (the display map of the Π-type of the two types that fullness supplies) and the bijection between the maps out of the pullback and the maps into it.
- `Cwa.LcccOfFull.transpose_naturality` — that bijection is natural in the slice object; the essential ingredient is the law `(λ b)[σ] = λ (b[σ⁺])` of a natural Π-structure, transported along the comparison of the two extended contexts.
- `LcccPullbacks.ofIsFull` — **the conclusion**: the category of contexts of a full model whose substitution on extended contexts is coherent and which carries a natural Π-structure is locally cartesian closed.

**3. A full model and the strictification of its own contexts** (new module `Start/CwaStrictifyFull.lean`). Sending a local universe to the presentation of its generic family, substituted along its classifying map, commutes with substitution *on the nose*, so it gives a morphism of models `Cwa.fullStrictify : Cwa.ofPullbacks C ⟶ T` which is the identity on contexts, is bijective on terms (`Cwa.fullStrictify_tmMap_bijective`), and hits every type of the model up to an isomorphism of extended contexts over the base (`Cwa.fullStrictify_essSurj`). For a full *democratic* model with dependent products the contexts also have a terminal object, so the strictification of the contexts is again a model with a natural Π-structure (`Cwa.nonempty_naturalPiStruct_ofPullbacks_of_isFull`).

**What is honestly still open.** A morphism of models in the other direction, `T ⟶ Cwa.ofPullbacks C`, would have to send a type over `Γ` to a local universe whose base and generic family do not depend on `Γ` — in effect a universe for the model — and none is constructed; so the remaining exit criterion of the task, an *equivalence* of a full democratic model with the strictification of its contexts in the lax 2-category, is not claimed. This is recorded verbatim as the task's open boundary.

**Verification.** `lake build` succeeds with zero linter warnings; `#print axioms` on all new headline results reports only `propext`, `Classical.choice`, `Quot.sound`; `python3 scripts/goal_state.py validate` gives "OK: 153 tasks validated" and `python3 scripts/check_closure.py` "OK: 387 modules, all in the import closure and all registered". The three new modules are imported by `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, described in `README.md`, and the task board, its evidence note and `docs/current-goal-state.md` are updated.

# Summary of changes for run 053d8195-442b-4afd-a963-a1fe1237cdd4
I picked the project up, repaired the build, and closed the last open item on the research queue.

**1. The repository builds again.** The checked-in dependency manifest disagreed with `lakefile.toml` and `lean-toolchain`, so nothing compiled ("dependency 'cslib' not in manifest"). The manifest is regenerated against Lean v4.33.0 / Mathlib `v4.33.0` with the matching revisions of every transitive dependency and of `cslib`. `lake build` now compiles the whole library — 9101 jobs — with no error and no linter warning, and there is no `sorry` or `admit` anywhere under `Start/`.

**2. The comparison with locally cartesian closed categories is now a biequivalence** (new module `Start/LcccBiequivalence.lean`). The library already had strictification as a pseudofunctor out of the 2-category of locally cartesian closed categories, proved locally fully faithful and locally essentially surjective; what was missing was the pseudofunctor back and the statement that the two are inverse.
- `Cwa.LcccModelCat` — the 2-category of the models those categories present: the full sub-2-category of models spanned by their strictifications, with all morphisms of models as 1-cells and all lax 2-cells as 2-cells.
- `Cwa.lcccStrictification` — strictification, corestricted to it.
- `Cwa.lcccCtx` — **the pseudofunctor back**. The functor on contexts of a morphism between strictified models preserves pullbacks, so it *is* a morphism of categories with pullbacks (`Cwa.ctxFnc`, `Cwa.ctxMap`), and a lax 2-cell is carried to its natural transformation; identities and composites are preserved on the nose, so the pseudofunctor is strict.
- `Cwa.lcccCtx_map_lcccStrictification_map` — one round trip is the identity on the nose (on 1-cells and on 2-cells); `Cwa.lcccStrictificationMapCtxMapIso` — the other is the identity up to a canonical invertible 2-cell, and no better, since strictification is not full on the nose.
- `Cwa.IsBiequivalence` (local equivalence plus bicategorical essential surjectivity) and `Cwa.lcccModelCat_biequivalent`: **both pseudofunctors are biequivalences**.

**3. Full and democratic models** (new module `Start/CwaDemocratic.lean`), which begins the intrinsic description of the models so compared: `Cwa.IsFull`, `Cwa.IsDemocratic`, the theorem that the category of contexts of a full model has pullbacks (`Cwa.hasPullbacks_of_isFull`, via `Cwa.IsFull.isPullback`), and the fact that every strictification is full and — with a terminal object — democratic.

**Verification.** `lake build` succeeds with zero linter warnings; `#print axioms` on all new headline results reports only `propext`, `Classical.choice`, `Quot.sound`; `python3 scripts/goal_state.py validate` gives "OK: 150 tasks validated" and `python3 scripts/check_closure.py` "OK: 381 modules, all in the import closure and all registered". Both new modules are imported by `Start.lean` and registered in `Start/Capstones.lean`.

**Bookkeeping.** `M10-CWA-BICATEGORY`, the last unfinished task, is now `DONE_STRONG` with an empty boundary and an updated evidence note. One new task, `M10-CWA-DEMOCRATIC`, records what is honestly still open: transporting a Π-structure on an arbitrary full model to a locally cartesian closed structure on its contexts (the existing proof is for the strictified model, where a type is a local universe), and comparing a full democratic model with the strictification of its contexts. `docs/current-goal-state.md` was re-rendered and `README.md` updated (task counts and a description of the new results). All work is committed and pushed.

# Summary of changes for run 25aa84f4-7e04-459f-b1ef-7df893d16762
I picked the project up where it stood, repaired the build, and added two new sorry-free developments to the complexity track.

**1. The repository builds again.** As committed, the checked-in dependency manifest (`lake-manifest.json`) named an older Mathlib and omitted `cslib` entirely, so it disagreed with `lakefile.toml` and `lean-toolchain` and nothing compiled ("dependency 'cslib' not in manifest"). The manifest is regenerated against Lean v4.33.0 / Mathlib `v4.33.0` with the matching revisions of every transitive dependency and of `cslib`. `lake build` now compiles the whole library — 9088 jobs, 368 modules — with no error and no linter warning, and there is no `sorry` or `admit` anywhere under `Start/`.

**2. Bounded-width satisfiability: `k`-SAT is NP-complete for every `k ≥ 3`** (new module `Start/ThreeSat.lean`). The library already had `SAT` and `CIRCUIT-SAT` as NP-complete problems; this adds the bounded-width one.
- `Complexity.Tseitin.length_le_three_of_mem_toCnf` — the Tseitin translation of a circuit only ever emits clauses of at most three literals, so the term that already reduces CIRCUIT-SAT to SAT lands in `k`-SAT for every `k ≥ 3` (`Complexity.polyManyOne_CSAT_KSAT`).
- Membership in NP needed a new ingredient: recognising, in polynomial time, that a word codes a CNF of width at most `w`. That is a finite-state property of the token code, so it is decided by an automaton (`Complexity.Sat.tdelta`) which is proved to simulate the decoder (`Complexity.Sat.rst_tdelta`) and is turned into a Cobham term (`Complexity.Sat.widthTerm`), giving `Complexity.Sat.inP_KCnfWord`.
- Conclusions: `Complexity.Sat.inNP_KSAT`, `Complexity.npHard_KSAT`, `Complexity.npComplete_KSAT`, and `Complexity.npComplete_ThreeSAT` for 3-SAT.

**3. `NP` is closed under intersection** (new module `Start/NPInter.lean`). The library had closure under union; intersection needs a witness carrying both witnesses. The classical self-delimiting pairing (first component with every bit doubled, marker `10`, then the second) is defined, its two projections are proved to undo it and to be finite-state transductions hence Cobham terms, and an arbitrary word is proved no longer than `2·|fst| + 3 + |snd|`, which keeps the witness bound polynomial — `Complexity.InNP.inter`. Along the way `Complexity.InNP.inter_inP` records closure of NP under intersection with P.

All headline results were checked with `#print axioms` and depend only on `propext`, `Classical.choice`, `Quot.sound`. Both modules are imported from `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, described in `README.md`, and carry task-board entries (`M11-THREE-SAT-NPC`, `M11-NP-INTERSECTION`, both complete) with evidence notes under `docs/goal/evidence/`; `docs/current-goal-state.md` was re-rendered and both project gates pass (`scripts/goal_state.py validate` — 145 tasks; `scripts/check_closure.py` — 368 modules, all in the import closure and all registered). Everything is committed and pushed.

Still open on the board, unchanged: the biequivalence between models with Π-types and locally cartesian closed categories, and the uniqueness clause of bi-initiality in the lax 2-category of models (whether two interpretation functors out of the syntax of λΠ admit at most one natural transformation). I investigated the latter and did not settle it: the obvious counterexample models are blocked by the pullback conditions a category with attributes imposes, and the rigidity argument for strict 2-cells does not transfer, so I left it open rather than record a half-proof. The untracked scratch files at the repository root are not part of the library target and were left untouched.

# Summary of changes for run 8ec91c74-6b04-4938-b972-a74526d8f6d3
Two things were asked for: put the project back on Lean v4.33.0, and carry the unfinished work further. Both are done, and everything is committed and pushed.

**1. The project builds against Lean v4.33.0 / Mathlib v4.33.0 again.** `lean-toolchain` had been reset to v4.28.0 while `lakefile.toml` still asked for Mathlib v4.33.0, so the checked-in dependency manifest and the toolchain no longer agreed and nothing compiled. The toolchain pin is back to `leanprover/lean4:v4.33.0`, the manifest is regenerated against the Mathlib `v4.33.0` tag with the matching revisions of every transitive dependency and of `cslib`, and `lake build` now compiles the whole library — 9080 jobs, 360 modules — with no error and no linter warning. The library contains no `sorry` and no added `axiom`.

**2. The lax 2-cells between morphisms of models now have their vertical and horizontal structure** — the next step on the one milestone the project's own board still had open, and both new modules are `sorry`-free with headline results depending only on `propext`, `Classical.choice`, `Quot.sound`.

*New module `Start/CwaLaxCategory.lean` — the lax 2-cells form a category.* Earlier work defined lax 2-cells (the equality of types of a strict 2-cell replaced by a map of extended contexts over the base) with an identity and a vertical composite, but never checked the laws. They are now proved: `Cwa.LaxTwoCell.id_vcomp`, `Cwa.LaxTwoCell.vcomp_id`, `Cwa.LaxTwoCell.vcomp_assoc`, packaged as the category `Cwa.laxMorCategory` on the morphisms `T ⟶ S`. The passage from a strict 2-cell to a lax one preserves identities and vertical composition and is injective, so it is a faithful functor out of the hom-category of strict 2-cells (`Cwa.laxInclusion`, `Cwa.TwoCell.toLax_injective`). The proofs rest on a new calculus for the substituted map of extended contexts: `Cwa.subOver_id`, `Cwa.subOver_comp`, `Cwa.subOver_eqToHom`, `Cwa.subOver_id_sub`, `Cwa.subOver_subOver`.

*New module `Start/CwaLaxWhisker.lean` — whiskering.* A lax 2-cell can be whiskered by a morphism of models on either side (`Cwa.LaxTwoCell.whiskerLeft`, `Cwa.LaxTwoCell.whiskerRight`), and both whiskerings preserve the identity lax 2-cell and vertical composition (`whiskerLeft_id`, `whiskerLeft_vcomp`, `whiskerRight_id`, `whiskerRight_vcomp`). Right whiskering needs the image of the comparison under the morphism, so the module also proves that a morphism of models carries the substituted map of extended contexts to the substituted map of the image (`Cwa.morOver`, `Cwa.morMap_subOver`, `Cwa.morOver_subOver`).

What is deliberately *not* claimed, and is recorded as the boundary: the interchange law between the two whiskerings — for lax 2-cells it would demand that the comparison of one 2-cell be natural in the component of the other, which is not part of the data — hence no bicategory of models with lax 2-cells, and the biequivalence with locally cartesian closed categories remains open, as before.

Both modules are imported from `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, described in `README.md`, and carry task-board entries (`M10-CWA-LAX-CATEGORY`, `M10-CWA-LAX-WHISKER`) with evidence notes under `docs/goal/evidence/`; `docs/current-goal-state.md` was re-rendered. The project's own gates pass: `scripts/goal_state.py validate` (139 tasks) and `scripts/check_closure.py` (360 modules, all in the import closure and all registered). The untracked scratch files at the repository root (`temp.lean`, `temp2.lean`, and similar) still contain `sorry`s; they are not part of the library target and were left untouched.

# Summary of changes for run 06217bc7-b92c-4b7a-84b5-71c3ae492063
I picked up the project where it stood and closed the work that was still open. Everything is committed and pushed; `lake build` compiles all 353 library modules (9073 jobs) with no error and no linter warning, and the library remains free of `sorry` and of any added `axiom`.

**1. Restored a working build.** The checked-in dependency manifest no longer matched what `lakefile.toml` and `lean-toolchain` ask for, so nothing in the project could be compiled at all (`dependency 'cslib' not in manifest`). The manifest is regenerated against Lean v4.33.0 / Mathlib v4.33.0 with the matching revisions of every transitive dependency and of `cslib`, and the whole tree builds from it.

**2. Application is preserved by the interpretation of λΠ** (`Start/LambdaPiInitialApp.lean`). The three statements that were left unproved in this module are now proved:
- `LambdaPi.val_app_weaken` — applying the weakening of a function to the generic argument returns the generic application, compared as a value;
- `LambdaPi.TmI.app_shift_var` — the raw term `(shift t) (var 0)` denotes the generic application of what `t` denotes;
- `LambdaPiInitial.tmMap_appQ` — application is preserved by the comparison morphism out of the syntactic model.

**3. The interpretation is a morphism of models, and the syntax is bi-initial** (new `Start/LambdaPiInitialModelHom.lean`). Preservation of application was the last clause a morphism of models required, so the comparison morphism is now packaged as `LambdaPiInitial.modelHom : ModelHom syntacticModel M` for every model with injective products. Combined with the previously proved rigidity of the hom-category this gives `LambdaPiInitial.biInitial_syntacticModel`: into every such model there is a morphism of models, and between the 1-cells underlying any two of them there is exactly one 2-cell. Previously only the uniqueness half was available, and only for a hypothetical morphism of models.

**4. Lax 2-cells, for which strictification is 2-functorial** (new `Start/CwaLaxTwoCell.lean`, `Start/CwaStrictLax.lean`). The project had established that strictification of a category with pullbacks cannot be 2-functorial for the strict 2-cells of models, and that any comparison must therefore weaken the morphisms or the 2-cells. This carries out the second weakening: `Cwa.LaxTwoCell` replaces the equality of types by a map of extended contexts over the base (with `Cwa.subOver`, identities and vertical composition, and every strict 2-cell exhibited as a lax one). A natural transformation of pullback-preserving functors then induces a lax 2-cell (`Cwa.laxTwoCellOfNatTrans`), functorially (`Cwa.laxTwoCellOfNatTrans_id`, `Cwa.laxTwoCellOfNatTrans_comp`); in particular the natural transformation that admits no strict 2-cell does admit a lax one (`Cwa.nonempty_laxTwoCell_id_coyoneda`).

`#print axioms` on all of the new headline results reports only `propext`, `Classical.choice`, `Quot.sound`.

**Bookkeeping.** The new modules are imported by `Start.lean` and indexed in `Start/Capstones.lean`; the project's own gates pass (`scripts/goal_state.py validate` — 134 tasks; `scripts/check_closure.py` — 353 modules registered). Two new task-board entries (`M10-LAMBDAPI-MODELHOM`, `M10-CWA-LAX-TWOCELL`) are recorded as complete with evidence notes in `docs/goal/evidence/`, the open boundary of the bicategory task is updated, `docs/current-goal-state.md` was re-rendered and `README.md` updated. What remains open on the board is the biequivalence between models with Π-types and locally cartesian closed categories: the lax 2-cells are not asked to be invertible, no bicategory structure is built for them, and on types the comparison is still only full up to isomorphism of presentations. The untracked scratch files at the repository root (`temp.lean`, `temp2.lean`, and similar) still contain `sorry`s; they are not part of the library target and were left untouched.

# Summary of changes for run 3e8768e7-d74d-4a93-af6b-1a985a3ce611
Two things were asked for: build against Mathlib v4.33.0, and finish the work that was left open. Both are done, and the library is green end to end.

**1. The library now really builds against Lean v4.33.0 / Mathlib v4.33.0.** The checked-in dependency manifest pinned an older Mathlib than `lakefile.toml` asked for, which is why 54 modules could not be compiled in the previous session. The manifest is regenerated against the `v4.33.0` tag (`db584cd6…`) with the matching revisions of every transitive dependency and of `cslib`. `lake build` now compiles all **9068 jobs / 348 library modules with 0 errors and 0 warnings** — including the entire Kolmogorov/algorithmic-information track that could not be compiled before. One deprecation warning that the newer Mathlib introduced (`push_neg`) was fixed at its source in `Start/LambdaPiEtaPostpone.lean`.

**2. The consolidation milestone that was still open on the project's task board is finished** — both of its entries, which were the only `TODO_READY` rows left.

*New module `Start/Rewriting.lean`* (sorry-free, no linter warnings; headline results depend only on `propext`, `Classical.choice`, `Quot.sound`) — abstract rewriting for an arbitrary relation `r : α → α → Prop`, replacing statements that were previously reproved between two and five times each:
- `Star`, `Plus`, `Alt`, `Conv`, `Joins` with the closure API (`trans`, `head`, `tail`, `single`, `mono`, `head_split`, `cases_head`, `star_congr`);
- `Diamond`, `Confluent`, `LocallyConfluent`, `Commute`, `StronglyCommute`, `Postpones`, `PostponesPlus`, `SN`, `Terminating`;
- `strip`, `confluent_of_diamond`, and `confluent_of_diamond_of_between` (the Tait–Martin-Löf argument through a parallel reduction);
- `conv_iff_joins_of_confluent` (Church–Rosser), `commute_of_stronglyCommute` (Hindley), `confluent_alt_of_commute` (Hindley–Rosen);
- `postpone_par_star`, `postpones_of_par`, `postponesPlus_of_par`, `star_alt_iff_of_postpones` (`(r ∪ s)* = r* ; s*`);
- `terminating_of_measure`, `sn_alt_of_postponesPlus`, `exists_normal_of_sn`, and Newman's lemma (`confluent_of_sn`, `confluent_of_newman`).

*Migration of the eight calculi named in the consolidation review* — `Reduction`, `SystemTConfluence`, `SystemFCConfluence`, `LambdaPi`, `LambdaBetaEta`, `LambdaEtaPostpone`, `LambdaPiEtaPostpone`, `LambdaPiEtaConfluent`. Each keeps its own inductive closure and adds a single bridging lemma (`reduces_iff_star`, `Red.iff_star`, `Conv.iff_conv`, `SRed.iff_plus`, and the erased-step relations `StepE`/`EtaStepE` for λΠ), after which confluence, the strip lemma, Church–Rosser, Newman, commutation, postponement and the strong-normalization transfer are obtained from the interface. Every public declaration name and statement of those modules is unchanged, so no downstream module was affected; the headline theorems were re-checked with `#print axioms` and still depend only on the standard axioms.

Integration and gates: the module is imported from `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, described in `README.md`, and carries two task-board entries (`M11-REWRITING-INTERFACE`, `M11-REWRITING-MIGRATE`, both `DONE_STRONG`) with evidence notes in `docs/goal/evidence/`; `docs/current-goal-state.md` was re-rendered. `scripts/goal_state.py validate` reports 132 tasks validated (130 `DONE_STRONG`), `scripts/check_closure.py` reports 348 modules all in the import closure and all registered, and no `sorry` or `admit` occurs anywhere under `Start/`. All work is committed.

Still open, unchanged and with their explicit boundaries on the board: `M9-LAMBDAPI-LCCC` (the biequivalence with locally cartesian closed categories) and `M10-CWA-BICATEGORY` (bi-initiality in the 2-category of all coherent models). The two research items from the earlier session that were never attempted — the hard half of Kolmogorov–Levin symmetry of information and further NP-complete reductions — remain unattempted; each is a substantial development rather than a batch of small lemmas, and I preferred to deliver the build repair and the consolidation milestone completely rather than leave a half-built counting argument behind.

# Summary of changes for run 6abb8520-3c21-4533-93e4-c5a02132210a
I took the four requested items in the order you gave them and finished item 1 completely (both the postponement technique and a real confluence theorem for λΠ), then did item 4 as a written investigation. Items 2 and 3 were not attempted; the reasons are below.

## 1. Typed η for λΠ — done, in two new sorry-free modules

**`Start/LambdaPiEtaPostpone.lean`** — the parallel-η + Hindley–Rosen technique of `Start/LambdaEtaPostpone.lean`, transported to λΠ.
- `LambdaPi.EtaPar`: parallel η-reduction (contracts a whole tower of η-expansions at once), with reflexivity, the inclusions to/from one-step η, and stability under renaming and substitution.
- `LambdaPi.EtaPar.lam_app_sred`: if `f` parallel-η-reduces to an abstraction, then `app f a` β-reduces in at least one step to a substitution instance — the step that fails for one-step η.
- `LambdaPi.betaEtaRed_iff` (also `LambdaPi.betaEta_postpone`): **βη-reduction of λΠ is β-reduction followed by η-reduction**.
- Typing-layer payoff: `LambdaPi.Typing.betaEta_sn` — **βη is strongly normalizing on typable terms** (β-SN from `LambdaPi.Typing.sn`, plus postponement, plus the fact that η shrinks a term), and `LambdaPi.Typing.hasBetaEtaNormalForm`.

**`Start/LambdaPiEtaConfluent.lean`** — the confluence lemma. The project already proves that raw βη is *not* confluent for λΠ (Nederpelt's term); this module shows the domain annotation is the only obstruction.
- `LambdaPi.eraseAnn` / `LambdaPi.Erased`: erasure of every abstraction's annotation to a fixed dummy sort, with the renaming/substitution lemmas and closure of erasedness under β and η.
- `LambdaPi.erased_step_eta_comm`: β and η **strongly commute** on erased terms; the critical case is exactly the one Nederpelt's term refutes for arbitrary annotations.
- `LambdaPi.erased_comm`, `LambdaPi.erased_betaEta_church_rosser`: hence β* and η* commute and **βη is confluent on erased terms** (Hindley–Rosen, using the postponement above).
- `LambdaPi.betaEtaConv_eraseAnn`, `LambdaPi.betaEtaConv_iff_join`: every term is βη-convertible to its erasure, so **two raw terms are βη-convertible exactly when their erasures have a common βη-reduct** — Church–Rosser for λΠ modulo annotations.
- The consequences the conversion rule needs, now for η-extended conversion: `betaEtaConv_sort_inj`, `not_betaEtaConv_sort_pi`, `betaEtaConv_pi_inv`.

Both modules build with no errors and no linter warnings, contain no `sorry`/`admit`, and their headline results depend only on `propext`, `Classical.choice`, `Quot.sound`. They are imported from `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, described in `README.md`, and carry two new task-board entries (`M10-LAMBDAPI-ETA-POSTPONE`, `M10-LAMBDAPI-ETA-CONFLUENT`, both `DONE_STRONG`) with evidence notes; `docs/current-goal-state.md` was re-rendered and both gates pass (`goal_state.py validate`: 132 tasks; `check_closure.py`: 347 modules, all in the import closure and registered).

## 4. Consolidation — investigated, written up as `docs/consolidation-review.md`

Three passes over the 347 modules (name-level, family-level, theory-level). Findings:
- **No public declaration is defined twice**; the only repeated qualified names are section-local helpers.
- The families that *look* duplicated are not: the realizability layers (`Assembly*`/`Modest*`/`PER*`) are related by the equivalence `perEquivModest` and by genuine extra content, and the Kolmogorov family has already been consolidated behind `DescriptionSystem.lean` — that is the pattern to imitate.
- The **one real duplication is abstract rewriting**: fourteen hand-rolled reflexive–transitive closures, four parallel-reduction/diamond/strip developments, Hindley–Rosen twice, η-postponement twice (writing the λΠ version by hand is what made it visible). The note lists the nine relation-generic statements and how often each is currently reproved, and proposes one module `Start/Rewriting.lean` plus a one-lemma bridge per client, with no public name changes. Two `TODO_READY` board entries (`M11-REWRITING-INTERFACE`, `M11-REWRITING-MIGRATE`) carry the plan.

## 2 and 3 — not attempted

- **Kolmogorov symmetry, hard half:** the Kolmogorov track (`KolmogorovDef`, `DescriptionSystem`, `KolmogorovMachines`, `KCMachine`, …) imports a Mathlib module that the Mathlib available to me does not provide, so those modules could not be compiled here at all; I did not want to add a counting argument I had no way to check.
- **More NP-complete reductions:** in this development a reduction has to be exhibited as an explicit Cobham (bounded-recursion) term with a correctness proof — the existing SAT encoding alone is about a thousand lines — so this is a substantial build rather than a batch of small lemmas, and I preferred to finish item 1 properly and deliver the consolidation study rather than leave a half-built reduction behind.

## Build note

The project pins Mathlib v4.33.0, while the Mathlib available in this session is older; 54 modules that use newer Mathlib APIs therefore could not be compiled here (this is pre-existing and unrelated to the new work — no λ-calculus or λΠ module is among them). The new modules and their whole dependency closure were built and verified. I also restored the dependency manifest, which was missing the `cslib` entry its own `lakefile.toml` requires, so `lake build` can resolve dependencies again. All work is committed.

# Summary of changes for run b1ee3272-a3e0-43de-9246-d8befe7f5fa5
I picked the project up where it stood, restored its build, and pushed the next item on its research queue through to completion.

**Build repair.** The checked-in dependency manifest (`lake-manifest.json`) had no entry for `cslib`, so `lake build` stopped immediately and nothing could be compiled. The manifest is regenerated against `lakefile.toml` — Mathlib at the `v4.33.0` tag, `cslib` at the revision built for Lean v4.33.0, plus the transitive dependencies — and the full library builds again with zero errors and zero warnings. I also shortened one over-long `open_boundary` field on the task board (`M9-LAMBDAPI-LCCC`), which was making `scripts/goal_state.py validate` fail; the content of the boundary is unchanged in substance.

**New module `Start/AssemblyProjective.lean`** (sorry-free, no linter warnings; results depend only on `propext`, `Classical.choice`, `Quot.sound`) — projective objects in the category of assemblies over a partial combinatory algebra:

- `partAsm`, `Partitioned`, `partitioned_partAsm` — an assembly is *partitioned* when every point has exactly one realizer.
- `RegularProjective`, `RegularProjective.of_iso` — projectivity with respect to the covers, i.e. the morphisms that lift realizers (the strong epimorphisms, as identified in the existing regularity module).
- `Partitioned.regularProjective` — a partitioned assembly is projective for those covers: the lift is tracked by the composite of the tracker of the map with the lifting combinator. This is the constructive content of choice in realizability.
- `coverAsm`, `coverHom`, `liftsRealizers_coverHom`, `exists_partitioned_cover` — every assembly is covered by a partitioned one (the pairs `(a, x)` with `a` a realizer of `x`), so `Asm(A)` has enough regular projectives.
- `exists_partitioned_iso_of_regularProjective`, `regularProjective_iff` — conversely a regular projective splits its cover, hence is isomorphic to a partitioned assembly: the regular projectives are exactly the assemblies isomorphic to partitioned ones.
- `Partitioned.prod`, `prodMapIso`, `RegularProjective.prod` — both classes are closed under binary products.
- Over Kleene's first algebra the two notions of projectivity are separated: `partitioned_natK1` and `regularProjective_natK1` (the standard numbers assembly is regular projective), `not_liftsRealizers_natToNabla` (the identity onto the indiscrete assembly on the numbers is an epimorphism that does not lift realizers, so epis and strong epis differ there), and `not_projective_natK1` (the non-computable diagonal function has no lift along it, so that assembly is not projective in the categorical sense).

**Integration.** The module is imported by `Start.lean` and registered in `Start/Capstones.lean` (explanatory paragraph plus `#check`s); prose was added to `README.md` and `Start/Demo.lean`; a new task-board entry `M10-ASM-PROJECTIVE` (DONE_STRONG) with evidence note `docs/goal/evidence/M10-ASM-PROJECTIVE.md` was added and `docs/current-goal-state.md` re-rendered, with the README badge and counts updated (128 tasks, 126 DONE_STRONG).

**Verification.** Full `lake build` completes with 0 errors and 0 warnings; `scripts/goal_state.py validate` reports 128 tasks validated; `scripts/check_closure.py` reports 345 modules, all in the import closure and all registered; no `sorry` or `admit` occurs anywhere under `Start/` or in `Start.lean`. All work is committed.

The two long-standing board items are unchanged, with their explicit open boundaries: `M9-LAMBDAPI-LCCC` (the biequivalence with locally cartesian closed categories is not claimed) and `M10-CWA-BICATEGORY` (bi-initiality in the 2-category of all coherent models, and the pseudofunctors to LCCCs, are not constructed).

# Summary of changes for run d2f09728-7ade-49a6-a2cd-83c3d9c7f580
Continued the project from its previous checkpoint and pushed the next research item through to completion, with the build and both project gates green throughout.

**New module `Start/AssemblyKleeneBool.lean`** (sorry-free, no linter warnings; results depend only on `propext`, `Classical.choice`, `Quot.sound`) — booleans, decidability and semidecidability in the category of assemblies over Kleene's first algebra `K₁`:

- `exists_index_of_partrec` / `exists_index_of_computable` — every (partial) recursive function of one variable is Turing application of a fixed index.
- `boolK1`, `modest_boolK1` — the standard assembly of booleans (`true` realized by `1`, `false` by `0`), and its modesty.
- `tracked_boolK1_iff`, `boolHomEquiv` — effective Church's thesis for boolean-valued functions: a function `ℕ → Bool` is tracked out of the standard numbers assembly exactly when it is computable, so those morphisms are in bijection with the computable boolean-valued functions.
- `exists_charBool_iff` — a predicate on the numbers has a characteristic morphism into the booleans exactly when it is a computable predicate.
- `not_computable_selfHalt`, `not_computable_selfHalt_false`, `no_charBool_selfHalt`, `boolK1_not_classifier` — self-halting is undecidable in both polarities, hence has no characteristic boolean map: the booleans of `Asm(K₁)` classify no sub-assembly cut out by an undecidable predicate, unlike the object of propositions already in the library.
- `rePred_iff_exists_index`, `rePred_selfHalt`, `not_computablePred_selfHalt` — a predicate is recursively enumerable exactly when it is the domain of convergence of a single element of `K₁`; self-halting is one, so it is semidecidable but not decidable.
- `boolOfSum`, `sumOfBool`, `boolK1IsoCoprod`, `falsePt`, `truePt`, `boolCofanIsColimit` — the booleans are nevertheless the coproduct `1 + 1`: their two points exhibit them as a coproduct of two copies of the terminal assembly (the coproduct tag is decoded effectively by applying it to `0` and then `1`).

**Integration**: the module is imported by `Start.lean` and registered in `Start/Capstones.lean` (explanatory paragraph plus `#check`s); prose was added to `README.md` and `Start/Demo.lean`; a new task-board entry `M10-ASM-KLEENE-BOOL` (DONE_STRONG) with evidence note `docs/goal/evidence/M10-ASM-KLEENE-BOOL.md` was added, and `docs/current-goal-state.md` re-rendered (126 tasks, 124 DONE_STRONG; badge and counts updated). While writing this up I also corrected a slight overstatement in the accompanying prose: the object of propositions classifies sub-assemblies (regular subobjects), not arbitrary monos.

**Verification**: full `lake build` completes with 0 errors and 0 warnings; `scripts/goal_state.py validate` reports 126 tasks validated; `scripts/check_closure.py` reports 343 modules all in the import closure and registered; no `sorry`/`admit` occurs anywhere under `Start/` or in `Start.lean`. All work is committed and pushed.

The two long-standing board items remain as before, with their explicit open boundaries: `M9-LAMBDAPI-LCCC` (BACKEND_PARTIAL — the biequivalence with locally cartesian closed categories is not claimed) and `M10-CWA-BICATEGORY` (DONE_WEAK — bi-initiality in the 2-category of all coherent models and the pseudofunctors to LCCCs are not constructed).

# Summary of changes for run 745a21b5-d18e-4261-9ea0-d2646c676b57
I picked up the project where it stood (already `sorry`-free, with the task board as its research queue) and pushed the next two items on that queue through to completion, in the realizability track.

**Build setup.** The checked-in dependency manifest no longer matched `lakefile.toml`, so nothing could be built. It is regenerated, and the full `lake build` now succeeds again (Lean v4.33.0, Mathlib v4.33.0) with no errors and no linter warnings.

**New module `Start/ModestEquiv.lean` — partial equivalence relations are the same thing as modest assemblies.**
- `Realizability.PER.Tracked` / `PER.Hom` / `PER.instCategory`: a function between the quotients of two PERs is tracked when a single element of the algebra computes it on representatives; this makes PERs a category. `PER.tracked_iff` proves that this intrinsic condition is exactly being tracked as a map of the presented assemblies.
- `Realizability.ModestCat` is the full subcategory of the modest assemblies; `PER.toModest` is the comparison functor and `PER.toModestFullyFaithful` shows it is fully faithful.
- `Assembly.toPERIso`: a modest assembly is isomorphic to the assembly of the PER it presents (both directions tracked by the identity combinator, since the two objects have the same realizers), giving essential surjectivity.
- `Realizability.perEquivModest : PER A ≌ ModestCat A`.
- `PER.arrowIso`: the arrow PER `R ⇒ S` presents the exponential of the two assemblies.

**New module `Start/ModestCcc.lean` — the modest sets, and hence the PERs, form a cartesian closed category.**
- `Assembly.Modest.of_iso`: modesty is invariant under isomorphism.
- The terminal assembly and the product of two modest assemblies are terminal and a product *in the subcategory* (`Modest.isTerminalUnitModest`, `Modest.prodFanModestIsLimit`), giving a cartesian monoidal structure with the product assembly on the nose.
- Currying is a natural bijection there (`Modest.curryEquivModest`, `Modest.instClosedModest`), so `Modest.instMonoidalClosed : MonoidalClosed (ModestCat A)`.
- Transported along the equivalence: the PERs have finite products and `PER.instMonoidalClosed`; `PER.toModestArrowIso` records that the comparison functor sends the arrow PER to the exponential.

**Verification and integration.** Both modules build with no `sorry`, no `axiom` and no linter warnings, and `#print axioms` on the headline results reports only `propext`, `Classical.choice`, `Quot.sound`. They are imported from `Start.lean`, registered with prose and `#check`s in `Start/Capstones.lean`, mentioned in `Start/Demo.lean` and described in `README.md`. Two new task-board entries (`M10-MODEST-PER-EQUIV`, `M10-MODEST-CCC`, both `DONE_STRONG`) with evidence files were added and `docs/current-goal-state.md` re-rendered. Both project gates pass: `scripts/goal_state.py validate` reports 107 tasks validated and `scripts/check_closure.py` reports 322 modules, all in the import closure and all registered. Everything is committed and pushed.

Still open on the board, as before: the two long-standing items `M10-CWA-BICATEGORY` (bi-initiality of the syntactic model of λΠ in full) and `M9-LAMBDAPI-LCCC` (the biequivalence with locally cartesian closed categories).

# Summary of changes for run 8eaa6a91-ba2f-458b-9943-07bb656ad45d
I continued and completed the outstanding piece of work in the project.

## New module: `Start/ArithBounded.lean`

Bounded quantifiers do not raise the level of the arithmetical hierarchy of `Start/ArithHierarchy.lean`. The module builds with no `sorry`, no `axiom` and no linter warnings, and its results depend only on `propext`, `Classical.choice` and `Quot.sound`.

What it proves:

- `Lambda.Arith.allLt` / `Lambda.Arith.exLt` — bounded conjunction and disjunction of a `Bool` test, defined by recursion on the bound, with characterizations (`allLt_eq_true_iff`, `exLt_eq_true_iff`) and computability uniform in the test (`computable_allLt`, `computable_exLt`).
- `Lambda.Arith.computablePred_ball_lt` / `computablePred_bex_lt` — the level‑zero case: the computable predicates are closed under `∀ y < b x` and `∃ y < b x` for computable `b`.
- `Lambda.Arith.sigmaAt_of_computablePred` / `piAt_of_computablePred` — a computable predicate sits at every level, on both sides.
- `Lambda.Arith.exists_code_of_ball_exists` — the **collection principle**: if every argument below a bound has a witness, one number codes a list of witnesses for all of them.
- `Lambda.Arith.sigmaAt_bounded_closure` — the main induction on the level, proving both bounded‑quantifier cases at once: collection pulls a bounded universal quantifier past the inner existential one, while a bounded existential is absorbed into the outermost existential quantifier; the `Π` halves follow by de Morgan.
- `Lambda.Arith.SigmaAt.ball_lt`, `SigmaAt.bex_lt`, `PiAt.ball_lt`, `PiAt.bex_lt` — the four closure theorems in usable form.

## Integration

The module is imported from `Start.lean` and `Start/Capstones.lean` (with a prose entry and `#check`s), advertised in `Start/Demo.lean`, and described in `README.md` (headline‑theorem block, survey bullet, task badge now 93/94). A new task‑board entry `M10-ARITH-BOUNDED` (`DONE_STRONG`) with `docs/goal/evidence/M10-ARITH-BOUNDED.md` was added and `docs/current-goal-state.md` re-rendered. Both project gates pass: `scripts/goal_state.py validate` reports `OK: 95 tasks validated` and `scripts/check_closure.py` reports `OK: 300 modules, all in the import closure and all registered`.

All work is committed and pushed.

## Notes

- Verification was carried out against the Mathlib available in this environment; the repository itself continues to ship its own pinned Lean/Mathlib configuration, which is unchanged by this work.
- The one task on the board that is not `DONE_STRONG` remains `M9-LAMBDAPI-LCCC`, whose documented open boundary is the biequivalence between models of λΠ and locally cartesian closed categories. Its modules could not be compiled with the Mathlib available here, so I did not attempt to change them; its status and open boundary are left exactly as they were.


# Summary of changes for run 341c9fba-973c-470f-850b-3bd5ff7d823d
The library is now finished: the whole project builds cleanly, contains no `sorry`, and both project gates pass.

**What was left open, and what I did**

1. **`Start/ArithHierarchy.lean` — the arithmetical hierarchy (was the last module with holes: 11 `sorry`s, and it was not yet in the import closure).** All of them are now proved:
   - `rePred_of_exists_computable`, `sigmaAt_one_iff` (Σ⁰₁ = the r.e. predicates), `piAt_one_iff` (Π⁰₁ = the co-r.e. predicates), `deltaAt_one_iff` (Δ⁰₁ = the computable predicates);
   - `computablePred_and`, `computablePred_or`, and `sigmaAt_closure` — closure of every level under conjunction and disjunction, by one induction whose step derives the dual Π-closure from the induction hypothesis by de Morgan — with `SigmaAt.and/.or`, `PiAt.and/.or`;
   - `SigmaAt.exists` and `PiAt.forall` — Σ⁰ₙ₊₁ is closed under existential and Π⁰ₙ₊₁ under universal quantification.
   To avoid duplicating a proof, `Lambda.Post.exists_test_of_rePred` was moved from `Start/ChaitinIncompleteness.lean` to `Start/PostSimple.lean`, next to the numbering of the r.e. sets it is proved from; the Chaitin module still obtains it by import.

2. **New module `Start/PostTheoremTwo.lean` — Post's theorem at level two**, joining the hierarchy with the previously proved Shoenfield limit lemma:
   - a limit is both a Σ⁰₂ and a Π⁰₂ statement (`deltaAt_two_of_limitComputablePred`);
   - conversely, a computable stagewise guess (bounded conjunction `allB`, bounded least witness `leastB`, `aliveUpTo`, `bestWitness`, `twoGuess`) that compares the least so-far-unrefuted witness on the two sides is proved computable and proved to settle on the correct answer (`limitComputablePred_of_deltaAt_two`);
   - `deltaAt_two_iff_limitComputablePred` : `Δ⁰₂ ↔ limit computable`, and with the limit lemma `deltaAt_two_iff_turingReducible_haltingOracle` : `Δ⁰₂` is exactly the class of predicates decidable from `∅′`.

3. **Integration and documentation.** Both modules are imported by `Start.lean` and registered in `Start/Capstones.lean` (prose plus `#check`s); the guided tour `Start/Demo.lean` gained a section on relative computability, the jump, the hierarchy and level-two Post; `README.md` gained a headline-theorem block and map entries for the oracle/jump/hierarchy material (and its task badge and counts were refreshed); four task entries with evidence notes were added to `docs/goal/task-board.yaml` / `docs/goal/evidence/` (covering the jump, the limit lemma, the hierarchy and level-two Post), and `docs/current-goal-state.md` was re-rendered.

**Verification**
- `lake build`: "Build completed successfully (9011 jobs)", no error and no warning.
- A search for `sorry`/`admit` over `Start/` and `Start.lean` returns nothing (the only textual matches are prose).
- `python3 scripts/goal_state.py validate` — OK, 92 tasks; `python3 scripts/check_closure.py` — OK, 291 modules, all in the import closure and all registered.
- Axiom audit of the new headline results (`sigmaAt_one_iff`, `deltaAt_one_iff`, `SigmaAt.exists`, `PiAt.forall`, `SigmaAt.and`, `deltaAt_two_iff_limitComputablePred`, `deltaAt_two_iff_turingReducible_haltingOracle`): only `propext`, `Classical.choice`, `Quot.sound`.

All work is committed and pushed.

# Summary of changes for run baff7410-e8a1-4f93-afe7-9d04e8ac9fdf
I picked up the in-flight work and carried the library to a complete, clean state.

**Repaired the build setup.** The dependency manifest no longer matched the lakefile (the local Mathlib/cslib checkouts), so nothing could be built at all; it is refreshed and the full `lake build` now succeeds (8323 jobs, 0 errors, 0 warnings, no linter messages).

**Finished the in-flight Myhill isomorphism module.** `Start/MyhillIso.lean` — one-one equivalent sets of numbers are recursively isomorphic (`Lambda.Myhill.recIso_iff_oneOneEquiv`), by the back-and-forth construction with a computable chase — was proved but only half integrated. It is now covered by an evidence note (`docs/goal/evidence/M10-MYHILL-ISO.md`), listed in the guided tour (`Start/Demo.lean`) and in `README.md`, and the task board validates again.

**Added a new completed result: the classification of the creative sets** (`Start/CreativeIso.lean`, new module, sorry-free):
- `Lambda.Post.exists_injective_productive` — a productive set has an *injective* computable production function. This is the missing ingredient, obtained by a chase: apply the production function, adjoin unusable values to the current r.e. set and repeat; the values produced are pairwise distinct, so the chase escapes any finite list of previously used values within one more step than the list is long, and it is computable.
- `Lambda.Post.exists_recursion_index_inj` — the recursion theorem with parameters, with an injective indexing.
- `Lambda.Post.oneOneReducible_of_productive_compl` — Myhill's theorem in one-one form: if the complement of `C` is productive, every r.e. set reduces to `C` by an injective computable function.
- `Lambda.Post.Creative.oneOneComplete`, `Lambda.Post.Creative.oneOneEquiv_haltK`, `Lambda.Post.creative_iff_oneOneComplete` — every creative set is one-one complete and one-one equivalent to Kleene's `K`.
- `Lambda.Post.Creative.recIso_haltK`, `Lambda.Post.Creative.recIso`, `Lambda.Post.creative_iff_recIso_haltK` — combining with Myhill's isomorphism theorem: a set is creative **exactly when** it is recursively isomorphic to `K`, and any two creative sets are recursively isomorphic.
- Concrete instances for the lambda calculus: the code sets for normalization, for convergence to a Church numeral, and for convertibility with a Church numeral are each recursively isomorphic to `K`.

**Integration and verification.** The new module is imported by `Start.lean`, registered in `Start/Capstones.lean`, listed in `Start/Demo.lean`, recorded on the task board as `M10-CREATIVE-ISO` with evidence in `docs/goal/evidence/M10-CREATIVE-ISO.md`, and described in `README.md`; `docs/current-goal-state.md` was re-rendered. Gates: `lake build` (whole library) and `lake build Start.Demo` succeed with no error or warning; `scripts/goal_state.py validate` reports 87 tasks validated; `scripts/check_closure.py` reports 286 modules, all in the import closure and registered; a search for `sorry`/`admit` under `Start/` finds none; and `#print axioms` on all the new headline results gives only `propext`, `Classical.choice`, `Quot.sound`.

The single remaining non-`DONE_STRONG` board entry is the pre-existing, explicitly declared open boundary (`M9-LAMBDAPI-LCCC`, the biequivalence between models of λΠ and locally cartesian closed categories), which I did not attempt. All work is committed and pushed.

# Summary of changes for run 123ddebc-33bf-4e83-be8d-5dce65b6c751
Continued the Lean library and left it building cleanly end to end.

**Finished the in-flight work (effective Rice theorem).** `Start/RiceCreative.lean` is now fully integrated: imported by `Start.lean`, registered in the capstone/closure gate `Start/Capstones.lean`, listed in `Start/Demo.lean`, given a task-board entry with an evidence note (`docs/goal/evidence/M10-RICE-CREATIVE.md`), and reflected in `README.md` (badge and task counts). Its headline results — a convertibility-invariant, inhabited class of lambda terms containing no unsolvable term has a code set with `HaltK ≤₀ CodeSet A` (`Lambda.manyOneReducible_haltK_codeSet`), a non-r.e. complement (`Lambda.not_rePred_compl_codeSet`), and creativity when r.e. (`Lambda.creative_codeSet`) — build without `sorry` and depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Added a new module, `Start/CreativeCodeSets.lean`,** supplying the enumerability half that the effective Rice theorem left open, and reading off the classification:
- `Lambda.reduces_of_conv_normal` — convertibility with a normal term is reduction to it;
- `Lambda.conv_church_iff_exists_nstep` — convertibility with a Church numeral is exactly the leftmost run reaching that numeral, giving a primitive recursive stage test (`Lambda.convChurchTest`, `Lambda.convChurchTest_primrec`);
- `Lambda.rePred_codeSet_conv_church` — that code set is recursively enumerable;
- `Lambda.creative_codeSet_conv_church`, `Lambda.manyOneEquiv_codeSet_conv_church_haltK`, `Lambda.not_simple_codeSet_conv_church` — it is creative, many-one equivalent to Kleene's `K`, and not simple;
- `Lambda.creative_codeHasNormalForm`, `Lambda.creative_codeConverges` and the corresponding many-one equivalences, including `Lambda.manyOneEquiv_codeHasNormalForm_codeConverges`.

The module is wired into `Start.lean`, `Start/Capstones.lean`, `Start/Demo.lean`, the task board (`M10-CREATIVE-CODESETS`) with evidence at `docs/goal/evidence/M10-CREATIVE-CODESETS.md`, and the README; `docs/current-goal-state.md` was re-rendered.

**Verification:** full `lake build` succeeds with 0 errors and 0 warnings (8994 jobs); `scripts/check_closure.py` reports 273 modules, all in the import closure and registered; `scripts/goal_state.py validate` reports 84 tasks validated (83 `DONE_STRONG`, the single `BACKEND_PARTIAL` entry being the pre-existing declared open boundary); no `sorry` occurs anywhere under `Start/` (only two prose mentions in a documentation comment); axiom audits of the new results show only `propext`, `Classical.choice`, `Quot.sound`.

All work is committed and pushed.

# Summary of changes for run 1162cc76-77d1-4e6e-823a-67a21b855520
## State of the project

The library is complete, builds cleanly and is `sorry`-free.

**Verification run in this session (all green):**
- `lake build` → "Build completed successfully (8977 jobs)", **0 errors, 0 warnings**.
- No `sorry` or `admit` anywhere under `Start/` (the only matches are the English word "admits" in prose).
- Gates: `python3 scripts/goal_state.py validate` → "OK: 78 tasks validated"; `python3 scripts/check_closure.py` → "OK: 256 modules, all in the import closure and all registered".
- Axiom audit on headline results (`Lambda.kolm_eq_iInf_kolmAt`, `LambdaPiCwa.not_piStruct_weakPi`, `CwaTypeNotClosed.not_piClosed`) → each depends only on `propext`, `Classical.choice`, `Quot.sound`.
- The CI workflows (`.github/workflows/`) contain no hard-coded toolchain version; they pick up `lean-toolchain`, which is now `leanprover/lean4:v4.33.0`. No stale references remained to fix.
- Working tree clean; `main` is pushed to `origin` (nothing left uncommitted).

**About the earlier toolchain question.** The copy of the project received here carried `lean-toolchain = leanprover/lean4:v4.28.0` from its very first commit, while `README.md`, the release notes and the evidence documents all described Lean `v4.33.0`. An earlier session had retargeted the pin to 4.28 so the project would build in a 4.28 environment, and rewrote several modules against the older Mathlib/`cslib` APIs. As you asked, the project has been moved back to **Lean v4.33.0**: the toolchain pin, the dependency checkouts (Mathlib at `6f1ef4e5dd`, `cslib` at `3951377e…`) and `lake-manifest.json` were restored, the affected modules were ported forward to the current APIs (Turing-machine `StateTransition` names, the encoding arguments that replaced the deprecated `FinEncoding`, bundled `TypeCat` homs, the new `cslib` β-reduction/`LcAt` interface), and all deprecation and linter warnings were cleared. The build result above is on that restored toolchain. The migration is recorded on the task board as `M10-TOOLCHAIN-V433-RESTORE` with evidence in `docs/goal/evidence/M10-TOOLCHAIN-V433-RESTORE.md`.

**What remains open, stated plainly.** Of the 78 tracked tasks, exactly one is not marked done: `M9-LAMBDAPI-LCCC` ("dependent types: λΠ, categories with attributes, locally cartesian closed categories"). All of its own exit criteria are met and evidenced — the syntax and metatheory of λΠ, its syntactic category with attributes and weak Π-structure (including the proof that η genuinely fails), the strictified model, the locally-cartesian-closed dependent product, universes with small products and product codes, the set-theoretic model, and the negative result that closure of a general universe under the pushforward product is genuine extra structure. What is *not* claimed, and is recorded in the task's open boundary, is **initiality**: an interpretation of the raw syntax into an arbitrary model with a universe, and hence any comparison between the syntax and an arbitrary model. I examined this again in detail rather than assuming the earlier assessment. Beyond its sheer size (a partial interpretation of raw syntax together with semantic renaming, substitution and conversion-soundness lemmas), there is a specific obstruction in this presentation: λΠ's application is unannotated, so the semantic value of `app f u` must recover the domain/codomain from the semantic type of `f`, which an arbitrary model's Π-former does not determine — even the "at most one interpretation" half is therefore entangled with the full conversion-soundness argument rather than separable as a cheap first step. Rather than start a development that could not be finished cleanly and would leave `sorry`s in a library whose defining property is that it has none, I left the boundary documented honestly and the project in its verified, complete state.


# Summary of changes for run bcd42189-9012-44ff-9669-268610d9b59e
Continued the project by completing and integrating a new development: **Kolmogorov complexity is upper semicomputable**.

New module `Start/KolmogorovApprox.lean` (sorry-free, warning-free, axioms limited to `propext`, `Classical.choice`, `Quot.sound`):

- `Lambda.progBy` — the time-bounded program test ("code `c` is a closed term whose leftmost-outermost run reaches the Church numeral of `s` within `k` steps"), proved primitive recursive (`progBy_primrec`), correct (`progBy_encode_iff`, `exists_isProgramFor_of_progBy`, `exists_progBy_of_isProgramFor`) and stable in the number of steps (`progBy_mono`).
- `Lambda.rePred_kolm_le` — the relation `K s ≤ n` is recursively enumerable.
- `Lambda.not_rePred_lt_kolm` — the complementary relation `n < K s` is *not* recursively enumerable (via the previously proved Chaitin incompleteness theorem plus the existence of incompressible numbers). Together with the existing `not_computablePred_kolm_le` this pins down the exact effective content of `K`: r.e. from above, not decidable, not r.e. from below.
- `Lambda.minAt` / `Lambda.kolmAt` — the stagewise approximation, proved primitive recursive (`primrec_minAt`, `primrec_kolmAt`), above `K` (`kolm_le_kolmAt`), non-increasing in the stage (`kolmAt_antitone`), exact from some stage on (`exists_kolmAt_eq_kolm`, `kolmAt_eventually_eq_kolm`), and hence `Lambda.kolm_eq_iInf_kolmAt : kolm s = ⨅ k, kolmAt s k`.

Supporting change: `Start/PostSimple.lean`'s sufficient condition for recursive enumerability (`Post.rePred_of_exists_test`) was generalized from predicates on `ℕ` to any `Primcodable` domain, so that it applies to pairs; all existing users still compile.

Integration and project gates: the module is imported by `Start.lean` and registered in `Start/Capstones.lean` (with prose and `#check`s), mentioned in the guided tour `Start/Demo.lean` and in `README.md` (badge and counts updated to 76/77), and recorded on the task board as `M10-KOLM-UPPER-SEMICOMPUTABLE` with evidence in `docs/goal/evidence/M10-KOLM-UPPER-SEMICOMPUTABLE.md`; `docs/current-goal-state.md` was regenerated. Verified: `python3 scripts/goal_state.py validate` (77 tasks OK), `python3 scripts/check_closure.py` (256 modules OK) and a full `lake build` with 0 errors and 0 warnings; no `sorry` remains in the new file. Everything is committed and pushed.

The only board item still not `DONE_STRONG` is the pre-existing `M9-LAMBDAPI-LCCC` (λΠ initiality / universes closed under pushforward product / η for λΠ), which was left untouched.

# Summary of changes for run 3c2af0af-7c6f-4d54-b64a-1e22e12dcc83
I continued the project by closing its main remaining open boundary: **full abstraction of Scott's `D∞` for the untyped λ-calculus (Wadsworth's theorem), now proved unconditionally.**

**Starting point.** Three modules — `Start/ApproxShape.lean`, `Start/DinfSpine.lean`, `Start/DinfTagBelow.lean` — were present but outside the entrypoint's import closure (the project's closure gate was failing on them). They supplied the shape lemma for finite approximants and the hardest case of the missing semantic principle, "a variable below a term", where the right-hand side may be an *infinite* η-expansion of the variable. What was still missing was the other half and the assembly.

**New file `Start/DinfTagBelowSound.lean` (no `sorry`).**
- `ScottDinf.le_ddenot_of_not_tagFail_approx` — *an approximant below a term*: a size induction on a finite approximant, driven by `Lambda.approx_direct_shape`. Either the approximant is dominated by an unsolvable term, hence denotes the least element, or it shares a spine with the term and the two nodes are compared after feeding both sides the same stack of arguments, which is legitimate because `D∞` is order-extensional. The arguments supplied by η-expansion are handed to the variable case.
- `ScottDinf.tagBelowSound` — the semantic principle `ScottDinf.TagBelowSound`, which the earlier conditional theorems had to assume: for closed terms, absence of a finite failure witness `Lambda.TagFail` implies the `D∞` inequality. The approximation theorem `ScottDinf.isLUB_ddenot_direct` lifts the previous lemma from approximants to arbitrary terms.
- `ScottDinf.separatesApprox` — the separation principle of `Start/DinfWadsworth.lean`, previously stated but unproved.
- `ScottDinf.ddenot_le_iff_not_tagFail_unconditional` — with the existing converse, the `D∞` order between closed terms *is* the absence of a failure witness.
- `ScottDinf.obsEqHnf_iff_ddenot_eq` — **Wadsworth's theorem**: two closed terms are observationally equivalent, by head normalisation, exactly when they have the same `D∞` denotation.
- `ScottDinf.obsEqHnf_iff_not_tagFail` — a finite-witness characterisation of observational equivalence itself, mentioning neither contexts nor the model.

Supporting lemmas added along the way: `Lambda.tagFail_of_reduces`, `Lambda.freeBelow_argTermOf`, `Lambda.argEnvT_lt_of_depth`, `ScottDinf.dappSeq_mono_lt`, `ScottDinf.argEnvD_match_len`.

**Housekeeping.** The three previously orphaned modules and the new one are wired into `Start.lean`, the capstone registry `Start/Capstones.lean` and the guided tour `Start/Demo.lean`; `README.md`, the task-board entry `M9-UNTYPED-FULL-ABSTRACTION` (now `DONE_STRONG`, empty open boundary) and its evidence file are updated, with the earlier evidence text preserved and marked as superseded where it described the statement as open. The dependency manifest was regenerated so that it matches the toolchain and the local package paths the project's lakefile declares.

**Verification.** `lake build` builds all 245 modules with no errors and no linter warnings; the project's two mechanical gates pass (`scripts/check_closure.py`: every module in the import closure and registered; `scripts/goal_state.py validate`: 70 tasks). No `sorry` in the library, and `#print axioms` on `ScottDinf.tagBelowSound`, `ScottDinf.le_ddenot_of_not_tagFail_approx`, `ScottDinf.separatesApprox`, `ScottDinf.obsEqHnf_iff_ddenot_eq` and `ScottDinf.obsEqHnf_iff_not_tagFail` reports only `propext`, `Classical.choice`, `Quot.sound`.

All work is committed and pushed. The one item still marked partial on the board is `M9-LAMBDAPI-LCCC` (initiality for `λΠ` and universes closed on the nose under the pushforward product), which is untouched by this run.

# Summary of changes for run 9b14a10a-f769-4bb0-b36e-2d1a9685252f
I continued the Lean formalization and added a new, fully verified result at one of the two remaining open boundaries of the task board, then cleaned up the build.

**New mathematics: `Start/DinfEtaLimit.lean` (new file, no `sorry`)**

The task board recorded, as an informal remark, that Scott's `D∞` identifies a term with its *infinite* η-expansion — which is why the residual semantic principle `ScottDinf.TagBelowSound` has to be phrased negatively (no relation generated by finite witnesses can decide the `D∞` order). That remark is now a theorem.

- `ScottDinf.eq_dId_of_eta_fixpoint` — **the identity of `D∞` is characterised by two η-limit equations**: if `x · y · z = y · (x · z)` for all `y, z` and `x · ⊥ = ⊥`, then `x` is the identity. Proved by two simultaneous inductions over the levels of the inverse limit (`psi_le_Phi_of_eta_fixpoint` and `theta_Phi_le_psi_of_eta_fixpoint`); no finite amount of η-expansion is assumed.
- `ScottDinf.Jterm` — the closed term `J = Θ (λ j x y. x (j y))` built from Turing's fixed-point combinator, with its defining reduction `ScottDinf.Jterm_reduces : J ↠ λx y. x (J y)`. Unfolding, `J` is the identity η-expanded infinitely often.
- `ScottDinf.ddenot_Jterm_eq_ddenot_id` — **`⟦J⟧ = ⟦I⟧` in `D∞`**, in every environment; hence `ScottDinf.obsEqHnf_Jterm_id` (no context distinguishes them) and `ScottDinf.ddenot_app_Jterm` / `ScottDinf.obsEqHnf_app_Jterm` (`J M` is indistinguishable from `M`, for every term `M`).
- `ScottDinf.not_conv_Jterm_I` — the identification is **not** a β-conversion: the graph model, which is sound for β and not extensional, separates `J` from the identity. So the `D∞` identification is genuine.

Reusable machinery developed for the proof and stated separately: `theta_le_iff` (the order at a finite level), `theta_succ_le_of_forall_psi` and `le_of_forall_psi` (extensionality criteria that only ever apply elements to the image of `psiFun n`), `Phi_psi_succ_app`, `Phi_bot_app_zero`, `psiFun_botD`, and an environment-independence lemma for closed terms. A dead end is recorded in the file: the naive strengthening `theta n (x · z) ≤ x · theta n z` is false in `D∞`.

`#print axioms` on all the headline results reports only `propext`, `Classical.choice`, `Quot.sound`.

**Housekeeping**

- Wired the new module into `Start.lean`, `Start/Capstones.lean` and the guided tour `Start/Demo.lean`; updated `README.md`, the task-board entry and the evidence note for the untyped full-abstraction item (`python3 scripts/goal_state.py validate` passes; `docs/current-goal-state.md` re-rendered).
- Cleared the five linter warnings that the current Mathlib raises: two deprecated imports (`Mathlib.Data.Nat.Lattice` → `Mathlib.Order.Lattice.Nat`), one deprecated lemma (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`), one over-long line in `Start/Kolmogorov.lean`, and the `checkUnivs` false positive on `Cwa.Model` (handled the same way Mathlib handles it for `CategoryTheory.Cat`, with an explanatory comment). `lake build` now emits no warnings from `Start/`.
- Documented in `lakefile.toml` and `README.md` the Mathlib revision the library is verified against.

**Verification**: `lake build` completes successfully (8962 jobs); there is no `sorry` or `admit` anywhere under `Start/`. The pre-existing scratch files at the repository root (`temp.lean`, `temp2.lean`, etc.) were left untouched.

**Still open** (unchanged, and recorded on the board): the semantic principle `ScottDinf.TagBelowSound` behind full abstraction of `D∞` for arbitrary terms, and initiality for `λΠ`. The new result settles the specific phenomenon that obstructs a finite-witness proof of the first, but not the principle itself.

# Summary of changes for run 697aa3cc-c3b7-42ac-8760-fc7f64408312
I continued work on the one substantive open item in the project, `M9-UNTYPED-FULL-ABSTRACTION`: full abstraction of Scott's `D∞` (Wadsworth's theorem). Previously the project reduced it to a single unproved principle, `ScottDinf.SeparatesApprox`, which mixed a *syntactic* Böhm-out (produce a separating context) with a *semantic* comparison. The syntactic half is now proved, so what remains is purely semantic.

**New: `Start/TagFail.lean`**
- `Lambda.TagFail` — a finite failure witness for the comparison of two *arbitrary* terms: along a path on which the η-expanded head normal forms agree, either the second term head-diverges where the first has a node, or the two η-expanded nodes have different head tags or different arities. Unlike the earlier tree-level development, the nodes of the second object are produced by head reduction rather than given by a Böhm tree.
- `Lambda.sepDiv_of_tagFail` — **the Böhm-out**: a failure witness yields a list of closed arguments on which the tagged instantiation of the first term head-converges while that of the second head-diverges. Because an arbitrary term carries no a priori arity bound, the tag bound and arity bound are produced bottom-up from the witness.
- Supporting results: substitution of closed terms commutes with reduction, one step of the descent driven by a head normal form (`Lambda.reduces_csub_node_eta`), and the identification of the η-expanded arguments of a node.

**New: `Start/DinfWadsworthSharp.lean`**
- `ScottDinf.TagBelowSound` — the remaining principle: for closed terms, *absence* of a finite failure witness implies `⟦M⟧ρ ≤ ⟦N⟧ρ`. It mentions no contexts and no separation, only the `D∞` order.
- `ScottDinf.separatesApprox_of_tagBelowSound` — it implies the old `SeparatesApprox`, hence `ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound`: full abstraction of `D∞` conditional on that one semantic statement.
- `ScottDinf.not_ddenot_le_of_tagFail` — the **converse**, proved unconditionally: a failure witness really does refute the `D∞` inequality. Consequently `ScottDinf.ddenot_le_iff_not_tagFail` is a characterisation modulo the remaining principle, and `ScottDinf.not_tagFail_self` shows no closed term admits a failure witness against itself, so the failure relation is not vacuously satisfiable and the reduction is not degenerate.

The earlier `Start/HeadSpine.lean` (spines, forward preservation of head normalizability, unsolvability under application and under substitution of closed terms, the one-sided separation `Lambda.SepDiv`) is what these build on.

`ScottDinf.TagBelowSound` is stated as the negation of an inductive relation on purpose: `D∞` identifies a term with its infinite η-expansions (for instance `x` with `Y (λf y. x (f y))`), which no inductively generated relation on finite witnesses can reach. It remains unproved — it is the hard core of Wadsworth's theorem — but it is an ordinary hypothesis, not an axiom, and no axiom is introduced anywhere.

Also done: both new modules were added to the root `Start.lean`; `docs/goal/evidence/M9-UNTYPED-FULL-ABSTRACTION.md`, `docs/goal/task-board.yaml` and `docs/current-goal-state.md` were updated to record the narrowed boundary (task-board validation passes); the new results are registered in the properties table.

Verification: `Start.HeadSpine`, `Start.TagFail` and `Start.DinfWadsworthSharp` compile with no errors, no linter warnings and no `sorry`; `#print axioms` on `Lambda.sepDiv_of_tagFail`, `ScottDinf.separatesApprox_of_tagBelowSound`, `ScottDinf.obsEqHnf_iff_ddenot_eq_of_tagBelowSound`, `ScottDinf.not_ddenot_le_of_tagFail` and `ScottDinf.not_tagFail_self` reports only `propext`, `Classical.choice`, `Quot.sound`. A whole-project build shows exactly the same set of failing modules as before this session (`Start/CobhamShift.lean`, `Start/InputSegment.lean`, `Start/TM2Partrec.lean`, `Start/TM2Forward.lean`, `Start/CwaType.lean`, `Start/CwaCat.lean`, `Start/CwaUnivLocal.lean`, plus one file in the `cslib` dependency); those failures are caused by the Mathlib snapshot available here being older than the one the project pins, and I left those files untouched.


# Summary of changes for run aec26334-24c5-447e-b6c3-31e925ec389a
本轮继续处理了任务板上仍未解决的那一项(`D∞` 的完全抽象 / Wadsworth 定理),并在其上取得了实质进展。所有改动均已提交并推送。

**已完成并通过编译、无 `sorry`、`#print axioms` 仅依赖 `propext, Classical.choice, Quot.sound` 的新结果**

1. `Start/DinfApply.lean` — `D∞` 中的迭代应用演算:`dappSeq`、`dappN`、`envStack`、`dappN_lamN`、`ddenot_appList`,以及外延性 `dinf_ext_dappN`(两个在 `m` 个参数上表现相同的元素相等)。

2. `Start/DinfBohmEta.lean` — **η 相等的 Böhm 树在 `D∞` 中同解释**(`ScottDinf.ddenot_toTerm_eq_of_tagEq`)。证明是对树对大小的归纳,逐步镜像 `Start/BohmEta.lean` 中 η 一般化的 Böhm-out 下降:每个结点两边喂入同一参数栈(靠 `D∞` 的外延性),标签相同的变量取相同的值(`envStack_match`),归纳假设作用于各参数。

3. `Start/DinfNormalFullAbstraction.lean`
   - `not_obsEqHnf_of_separable`:可分离的项在观察上可区分,分离上下文取 `C[X] = X a₁ … aₖ Ω I`(一侧归约到 `Ω`,另一侧归约到 `I`)。
   - `obsEqHnf_iff_ddenot_eq_normal`:**闭 β 范式上的完全抽象** —— 观察等价 ⟺ 在每个环境下 `D∞` 解释相等(Wadsworth 定理的有限情形)。
   - `obsEqHnf_iff_ddenot_eq_of_normalizes`:推广到所有具有 β 范式的闭项。
   - `ddenot_eq_of_obsEqHnf_of_not_hasHnf`:另一端的情形 —— 无头范式的项。

4. `Start/DinfWadsworth.lean` — 把剩余缺口精确化:证明了上下文对洞的单调性 `ddenot_fill_mono`,陈述(**未证明**)近似式分离原理 `SeparatesApprox`,并在其之上**有条件地**证出全体闭项的完全抽象 `obsEqHnf_iff_ddenot_eq_of_separatesApprox`。该原理只是一个普通的显式假设,没有引入任何 `axiom`。

**仍未解决(如实记录)**:`D∞` 对任意项的完全抽象(完整的 Wadsworth 定理)。缺的正是 `SeparatesApprox`:含 `Ω` 的有限近似式的分离论证,超出本项目中针对 β 范式的 Böhm 分离理论。

**其他**:新文件已加入 `Start.lean`;`docs/goal/task-board.yaml` 的 `M9-UNTYPED-FULL-ABSTRACTION` 开放边界、`docs/goal/evidence/M9-UNTYPED-FULL-ABSTRACTION.md`、`docs/current-goal-state.md`(重新生成)与 `README.md` 均已更新,如实区分「已证」与「未证」;`python3 scripts/goal_state.py validate` 通过(67 项)。`ARISTOTLE_SUMMARY.md` 未作改动。

**环境说明**:本环境可用的 Mathlib 与项目 `lean-toolchain` 所固定的版本不一致,项目中若干与新版 Mathlib 绑定的文件(如 `Start/CwaType.lean`)以及随附的 `cslib` 依赖在此处无法编译 —— 这是既有情况,与本轮改动无关;上述所有新文件及其全部依赖闭包均编译通过。

# Summary of changes for run fee6a6b0-1516-48b9-b2a7-33ebfd9c1455
继续完成了项目中此前明确标记为未解决的一个数学缺口:Scott 图模型的**逼近定理**。

## 新增内容:`Start/GraphApproxTheorem.lean`(已加入 `Start.lean`)

此前 `Start/GraphApprox.lean` 只证明了逼近定理的"容易的一半"(所有归约项的直接逼近式的指称都包含在项的指称中),反方向被明确记为未解决。现在两个方向都证明了:

- `GraphModel.exists_reduct_mem_denot_direct` — `⟦M⟧ρ` 中的每个 token 都已经属于某个归约项 `M'` 的直接逼近式的指称 `⟦ω(M')⟧ρ`;
- `GraphModel.denot_eq_iUnion_denot_direct` — **逼近定理**:`⟦M⟧ρ = ⋃ {⟦ω(M')⟧ρ : M ↠ M'}`;
- `GraphModel.exists_reduct_denot_direct_sup` — 逼近式构成有向族,故上式的并确为上确界;
- `GraphModel.denot_subset_of_approx_reducts` / `denot_eq_of_approx_reducts` — 推论:逼近式(Böhm 树)之间的语法支配关系蕴涵语义包含关系,互相支配的两项被模型等同。

证明方法:Kripke 式可计算性(逻辑关系)论证,形式上与 `Start/GraphAdequacy.lean` 的充分性证明相同,但携带逼近式信息。谓词 `ARealAux b ρ t` 按 token 的大小递归定义;`AReal` 把它对环境的弱化封闭。与充分性证明不同的是,这里语义环境必须与语法环境同步弱化,因此基本引理 `arealAux_substEnv` 同时涉及两个环境:一个解释项的自由变元,一个解释代换的目标语境。两个语法性的辅助结果支撑该论证:直接逼近式沿归约只增不减(`denot_direct_reduces_mono`,注意由于 `Ω` 在此是普通项而非常量,逼近序 `Lambda.Approx` 并不传递,所以链接是在指称层面完成的),以及由合流性把有限多个归约项合并为一个(`exists_reduct_lset_subset`)。

## 验证

- `lake build` 全量成功(8940 个作业),**零错误、零警告**;
- `Start/` 下无 `sorry`/`admit`;
- `#print axioms` 对两个主要结果仅报告 `propext, Classical.choice, Quot.sound`;
- `python3 scripts/goal_state.py validate` → OK: 67 tasks validated。

## 文档

更新了 `README.md`(语义章节新增逼近定理条目,并修订了 open questions 表中关于完全抽象的一行)、`docs/goal/evidence/M9-UNTYPED-FULL-ABSTRACTION.md`(新增一节说明证明结构)、`docs/goal/task-board.yaml` 中该任务的 open_boundary,并重新生成了 `docs/current-goal-state.md`。同时提交了上一阶段遗留的、关于恢复 Lean v4.33.0 工具链的文档改动。

## 仍然未解决

`D∞` 的完全抽象(Wadsworth 定理)仍未证明;经典证明所需的 `D∞` 版逼近定理本文未涉及。这一点已如实记录在任务板与证据文档中。

所有改动均已提交并推送。

# Summary of changes for run 3ddf95eb-7afb-4056-a71a-369c94723917
I picked up the in-progress work and completed it, then extended it with a stronger result. Everything is committed and pushed; the full library builds cleanly (`lake build`, 8242 jobs) with no `sorry` in any library file, and all new results check with `#print axioms` against only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Finished the in-progress module `Start/LambdaPiSmallCompare.lean`.** The project had two syntactic models of the dependent calculus λΠ built on the same category of contexts: the model of `Start/LambdaPiCwa.lean`, whose types in a context are the *small types*, and the small fragment of the model of `Start/LambdaPiFull.lean`, whose types are the *terms of the sort* `∗`. The new module compares them:

- `LambdaPiUniv.smallToCwa` — a morphism of categories with attributes from the small fragment to the model of small types: the identity on contexts, and on types the bijection between the terms of `∗` and the small types. The hard part, compatibility with the action of a substitution on extended contexts, is proved by showing that both sides act at every variable as the lifting `up` of the calculus.
- `LambdaPiUniv.smallToCwa_tyMap_bijective` — its action on types is a bijection in every context.

**Went further than the handoff plan and proved the two models isomorphic.**

- `LambdaPiUniv.cwaToSmall` — the comparison in the other direction, coding a small type as a term of `∗`.
- `LambdaPiUniv.smallToCwa_comp_cwaToSmall` and `LambdaPiUniv.cwaToSmall_comp_smallToCwa` — both composites are the identity morphism.
- `LambdaPiUniv.smallModelIso` — consequently the two syntactic models are isomorphic objects of the category of models of a dependent type theory. To state this I added one general, reusable extensionality lemma, `Cwa.heq_iso_ext`, to `Start/CwaCat.lean`.

**Bookkeeping.** The module is now imported by `Start.lean`. The task board, its evidence file for the λΠ / locally-cartesian-closed task, the rendered goal-state document and the README were all updated to describe the new comparison and to sharpen the boundary statement: what remains unclaimed there is the interpretation of the syntax into an arbitrary model (initiality) and any comparison between the syntax and an arbitrary model — the new isomorphism relates the two *syntactic* models to one another. The project's own validation gate (`scripts/goal_state.py validate`) reports 66 tasks validated. The Properties table has been updated with the new definitions and theorems, plus two earlier lemmas about the restriction of universe-preserving comparisons that had not been registered.

Two items on the board remain open by design and are documented as such: the initiality/interpretation theorem for λΠ, and full abstraction for the untyped calculus. Both are large developments in their own right rather than loose ends.

# Summary of changes for run 9c09982e-35ce-45db-9ab2-ac1339945fc3
I continued the formalization work on the project's one substantively open complexity-theory item (the Cook–Levin milestone), completing an increment that was left half-finished, and then extended it.

**What is new, all building with no `sorry` and no linter warnings:**

- `Start/UniformLayerPad.lean` — the layer and grid rules for P-uniform circuit descriptions with a *parameter word of their own*: the gate-writing Cobham term receives an arbitrary Cobham-computed word `pw n` in place of `1^n`, so a gate token need only be of length linear in the gate identifier and in `|pw n|`. This is what makes long tokens (references to gates whose identifiers are polynomial in `n`) admissible.
- `Start/UniformSelect.lean` — `selTokTerm`, a Cobham term that, from the code of a circuit and a gate identifier in unary, writes the token of that gate (`eval_selTokTerm_lt`). This is the first rule here that emits gates it is *given*, rather than gates computed by arithmetic on the identifier.
- `Start/UniformIterate.lean` — `iterC B D w k`, the stack of `k` copies of a stage circuit `B` over a base `D`, each copy's inputs rewired to the topmost `w` gates below; it is well formed (`wf_iterC`), its top `w` gates carry the `k`-th iterate of the stage's step function (`state_iterC`), and its output is read off that state (`out_iterC_state`). The main result **`codeUniform_iterC`** shows the stack is P-uniform whenever the stage and base are and the number of copies and the width are Cobham-computable in unary — the loop rule whose body is itself a circuit family, which is the shape the unrolling of a bounded recursion has.
- `Start/UniformIterLang.lean` — the same rule packaged as a statement about languages: `pUniformDecidable_iterLang` and `polyManyOne_SAT_iterLang`.
- `Start/UniformIterateInst.lean` — a non-vacuity instance whose stage really grows with the instance: a shift register with an accumulator of `n + 2` wires, proved to shift correctly (`stateC_sreg`) and to output the disjunction of all input bits after `n` copies (`out_sregC`), giving `pUniformDecidable_someOne_of_iter` and `polyManyOne_SAT_someOne_of_iter`.

**Verification.** The full library target builds cleanly (`Start.lean` now imports the five new modules); a search confirms no `sorry` in the new files; and the new results depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Documentation.** I extended the Cook–Levin evidence file with a section on unrolling a loop whose body is a circuit and refreshed its Boundary section, updated the corresponding task-board entry and re-rendered `docs/current-goal-state.md` (the board validator passes), and updated `README.md`. `ARISTOTLE_SUMMARY.md` was left untouched.

**What remains open** (unchanged in substance): there is still no compiler turning an arbitrary Cobham term into a stage circuit together with a number of copies, so no language is known to be P-uniformly decidable merely from being in P, and `NPHard` is still not known to be inhabited. The new iteration rule supplies the structural ingredient such a compiler needs for bounded recursion.

All work is committed and pushed.

# Summary of changes for run c2b99bc0-89bb-49b6-a91f-970f5ff82543
## What I did

I continued the open work on the Cook–Levin task, generalising the project's P-uniform circuit results from finite automata and symmetric languages to **automata with polynomially many states**, and then derived the two earlier families back as instances.

### New Lean files (all compile, no `sorry`, no warnings)

- **`Start/UniformState.lean`** — for an automaton with `M` states on inputs of length `n`, builds the circuit `CircCode.stGrid`: `M` columns (one per state), one block of `2M + 4` rows per input bit, then an acceptance row. Inside the block of bit `t` the one-hot vector of the state is recomputed from the previous one: for each target state a conjunction row selects, per source state, the constant `true`, the bit, its negation or the constant `false`, and an accumulator row takes the disjunction. Proves the one-hot bits really record the state (`lval_st_state`) and that the grid accepts exactly the automaton's language (`out_stGrid`).
- **`Start/UniformStateCode.lean`** — writes the description of that grid with a single Cobham term (`CircCode.stBlkT`, `eval_stBlkT`), bounds the size of every gate (`length_encGate_stT`), and concludes that the family is P-uniform (`codeUniform_stGrid`). Main results: `pUniformDecidable_stateLang` — **the language of a uniform poly-state automaton is decided by a P-uniform circuit family** — and `polyManyOne_SAT_stateLang`, its unconditional polynomial-time reduction to SAT. The uniformity hypothesis is packaged as `StateUniform`: the state count, both branches of the transition function and the acceptance predicate are computed in unary by Cobham terms.
- **`Start/UniformStateSubsume.lean`** — derives the two earlier families from the new rule: `pUniformDecidable_autoLang_of_state` (a finite automaton has finite transition and acceptance tables, selected by `Cob.tableSel`) and `pUniformDecidable_symLang_of_state` (a symmetric language is the language of the counting automaton, whose state is the number of `true` bits read so far, capped at the input length).
- **`Start/UniformStateInst.lean`** — a new instance that is neither regular nor symmetric: the words whose binary value, most significant bit first, is divisible by their length plus one (`BinDivLang`). The automaton keeps the value read so far modulo `n + 1`, so it has `n + 1` states; `pUniformDecidable_binDiv` and `polyManyOne_SAT_binDiv` conclude.

All four modules are imported from `Start.lean`; the full `lake build` succeeds, the project contains no `sorry`, and the new theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

### Bookkeeping

Updated the task board's open boundary for the Cook–Levin task, re-rendered `docs/current-goal-state.md`, extended `docs/goal/evidence/M9-COOK-LEVIN.md` with a section on the new construction, and updated `README.md`. `python3 scripts/goal_state.py validate` reports OK on all 60 tasks. Everything is committed and pushed.

### What remains open

The Cook–Levin task stays partial: the missing piece is still the compiler itself — a P-uniform circuit family for an *arbitrary* Cobham term — so no language in `P` is yet known to be P-uniformly decidable in general. The new rule enlarges the class that is known unconditionally, but only to one-way machines with polynomially many states. The other partial task (λΠ and locally cartesian closed categories) is untouched; its open boundary is the biequivalence between models of λΠ and LCCCs, which is beyond its stated exit criteria.

# Summary of changes for run 9b991d9b-3ec0-4a87-9e98-c2246b077ee3
I picked up the project where the previous session left off and carried the open Cook–Levin line forward. The project builds cleanly and all gates pass.

**State of the project**
- `lake build` completes successfully (8174 jobs), with zero errors and zero warnings.
- `python3 scripts/goal_state.py validate` reports `OK: 60 tasks validated`.
- There is no `sorry`, no `axiom`, and no `@[implemented_by]` anywhere in `Start/`. Spot-checked new results with `#print axioms`: they depend only on `propext`, `Classical.choice`, `Quot.sound`.

**New work this session**

1. `Start/UniformBool.lean` — *Boolean combinations of P-uniform circuit families.* This completes the algebra of P-uniform circuit descriptions with the one connection that was missing: joining the **outputs** of two circuits by a single gate.
   - `Tseitin.stackC` (one circuit on top of another, references relocated), with `out_stackC`;
   - `Tseitin.negC`, `conjC`, `disjC`, with their semantics (`out_negC`, `out_conjC`, `out_disjC`) and well-formedness (`wf_negC`, `wf_conjC`, `wf_disjC`);
   - two general tools — `exists_lenTerm` (a Cobham term writing the gate count of a P-uniform family in unary) and `codeUniform_gate` (a one-gate family is P-uniform when its tag is constant and its fields are unary Cobham functions);
   - `codeUniform_negC`, `codeUniform_conjC`, `codeUniform_disjC`: **the Boolean combinations of P-uniform families are P-uniform.**

2. `Start/UniformDecide.lean` — *languages decided by P-uniform families, and their unconditional reduction to SAT.*
   - `Tseitin.Pinned` and `PUniformDecidable L`: some P-uniform family of well-formed, nonempty circuits decides `L` on the inputs that present a word of length `n`.
   - `polyManyOne_SAT_of_pUniformDecidable`: **every P-uniformly decidable language reduces to SAT in polynomial time** — the Cook–Levin reduction with no hypothesis left over.
   - Closure: `PUniformDecidable.not`, `.and`, `.or`, `.congr`, plus the two constants `pUniformDecidable_true` / `pUniformDecidable_false`.
   - Two nontrivial inhabitants, so none of this is vacuous: `AllOnes` (all bits `true`), decided by `allOnesC` built from the conjunction circuits; and `SomeOne` (at least one bit `true`), decided by `someOneC` built from the block-loop family. Hence `polyManyOne_SAT_allOnes` and `polyManyOne_SAT_someOne`, both unconditional.
   - `npHard_SAT_of_pUniformDecidable` / `npComplete_SAT_of_pUniformDecidable`: SAT is NP-hard, hence NP-complete, as soon as every language in NP is decided by a P-uniform family — a second non-vacuous conditional form, stated about languages rather than verifiers.

3. Both modules were added to the `Start` aggregate, and the goal-state documentation was brought up to date: the `M9-COOK-LEVIN` evidence file gained a section on the new results, its task-board boundary was rewritten accordingly, and `docs/current-goal-state.md` was re-rendered.

**What remains open.** The two `BACKEND_PARTIAL` items are unchanged in status, because their residual content is genuinely open here: for `M9-COOK-LEVIN`, the explicit compiler turning a Cobham verifier into a description-writing term (so `NPHard` is still not known to be inhabited); for `M9-LAMBDAPI-LCCC`, the interpretation of the syntactic category with attributes into an arbitrary strictified model. What this session changed for the former is that the *reduction* half of Cook–Levin is now available unconditionally, so only the construction of the deciding family is still missing.

The Properties table has been updated with the new deliverables and their verified statuses.

# Summary of changes for run 4f57ff8f-3e4d-449b-81a2-76028142dd61
## What I did this session

I continued the Lean formalization from where the previous run left off. The build gate (`lake build`) and the project's own gate (`python3 scripts/goal_state.py validate`, 60 tasks) both pass, the whole library compiles with **no errors and no warnings**, and there is no `sorry` anywhere in the `Start` library.

All of the new work targets the one remaining gap in the Cook–Levin task: turning circuit families into families whose *descriptions* are produced in polynomial time (P-uniformity).

### New: a nontrivial P-uniform family (`Start/UniformAnd.lean`)

`CircCode.andCirc n` is built from two layers — `n` input gates, and above them `n` conjunction gates accumulating the running conjunction. Proved:

* `CircCode.wf_andCirc` — the circuits are well formed;
* `CircCode.out_andCirc` — the output is the conjunction of the first `n` input bits;
* `codeUniform_andCirc` — a single Cobham term writes the description of `andCirc n` from any word of length `n`.

So the P-uniformity predicate is inhabited by a linear-size family that decides a nontrivial language, not just by the previously available chain of negations.

### New: relocation and stacking (`Start/UniformShift.lean`)

Concatenating descriptions is not concatenating circuits — gates are numbered from the bottom of the list, so putting `C` above `D` shifts every identifier of `C`. `Tseitin.reloc d C` repairs this by raising every gate reference by `d`. Proved:

* `Tseitin.vals_reloc_append`, `Tseitin.out_reloc_append`, `Tseitin.wf_reloc_append` — semantics and well-formedness survive stacking;
* `CircCode.eval_relocTerm` — relocation is a Cobham function *of the description*: one term, run over the code with the shift in unary as parameter, rewrites every token;
* `codeUniform_reloc` and `codeUniform_stack` — **two P-uniform families may be written into one circuit.**

### New: composition (`Start/UniformCompose.lean`)

`Tseitin.reroute d e C` relocates `C` and additionally rewires its circuit inputs, so input `i` of `C` becomes a reference to gate `i + e` of the circuit underneath. Proved:

* `Tseitin.vals_reroute_append`, `Tseitin.out_reroute_append`, `Tseitin.wf_reroute_append` — the composite runs the upper circuit on the values of the lower one (under an explicit input-range condition, `Tseitin.inpsLt`);
* `CircCode.eval_rerouteTerm` — rewiring is again a Cobham function of the description, with the two shifts packed into one parameter word;
* `codeUniform_reroute` and `codeUniform_compose` — **two P-uniform families may be composed.**

Both operations are exercised on concrete families: the conjunction circuits placed beside the negation chain (`CircCode.andOverNeg`, with `out_andOverNeg` and `codeUniform_andOverNeg`) and fed by it (`CircCode.andAfterNeg`, with `out_andAfterNeg` and `codeUniform_andAfterNeg`).

### Documentation

`Start.lean` imports the three new modules. `docs/goal/evidence/M9-COOK-LEVIN.md` gained two sections describing the new families and the two composition operations, and the task board's `open_boundary` for that task was updated (it stays within the project's length limit); `docs/current-goal-state.md` was regenerated. `ARISTOTLE_SUMMARY.md` was left untouched.

## What is still open

The project is not fully closed. Two of the sixty tasks remain partial, and I did not change their status:

* **M9-COOK-LEVIN.** NP-hardness of SAT is still derived from the hypothesis `Complexity.PUniformAcceptFamilies`, which is nowhere assumed. Closing it means turning the existing chain of *existence* lemmas that compiles Cobham verifiers into circuits (`Start/CircuitBuild.lean`, `Start/WordCircuit.lean`, `Start/CobhamCircuit.lean`, `Start/CobhamBRec.lean`) into an explicit code-emitting compiler. The work above supplies the algebra such a compiler needs — constants, concatenation, layers, relocation, stacking, composition — but not the compiler itself.
* **M9-LAMBDAPI-LCCC.** The biequivalence between models of λΠ and locally cartesian closed categories (an interpretation functor into an arbitrary strictified model, plus an inverse comparison) is still not claimed. I did not work on it this session; it is a large development in its own right.

Existing scratch files at the repository root (`temp.lean`, `temp2.lean`, and similar) still contain `sorry`s; they are not part of the `Start` library target and I left them as they were.


# Summary of changes for run 35036ebb-213a-4dcb-8df3-4bd73ff82afd
## What I did

I continued the one substantially open item on the project's task board, **M9-COOK-LEVIN**, and closed the largest part of its gap.

Previously the library had SAT ∈ NP and the Tseitin translation from circuits to CNF, but the *compilation step* — turning an arbitrary polynomial-time (Cobham) verifier into a Boolean circuit — was only stated as a hypothesis (`Complexity.CircuitCompilable`). That step is now formalized.

### New results (all sorry-free, no extra axioms beyond `propext`, `Classical.choice`, `Quot.sound`)

* **`Complexity.Tseitin.cobCompiles`** (`Start/CobhamBRec.lean`) — **every Cobham term is computed by Boolean circuits of polynomial size.** The compiler handles projections, the empty word, the two successors, the smash function, composition and bounded recursion on notation. The hard case is bounded recursion: the recursion argument is unknown at compile time, so the step is unrolled once per position and multiplexed against the value carried over; this is affordable because, in the chosen word representation, dropping a prefix costs no gates at all.
* **`Complexity.Tseitin.exists_decideCircuit`** (`Start/PolyCircuit.lean`) — **P ⊆ P/poly**: for every polynomial-time term there is a monotone polynomial size bound and, for each length bound `N`, a well-formed circuit deciding it on all words of length ≤ `N`.
* **`Complexity.Tseitin.exists_npCircuitFamily`** — for every language in NP, a family of well-formed circuits of size polynomial in the instance length, satisfiable exactly on the language.
* **`Complexity.npHard_SAT_of_uniform` / `npComplete_SAT_of_uniform`** (`Start/CookLevin.lean`) — SAT is NP-hard, hence NP-complete, under the strictly weaker remaining hypothesis `Complexity.UniformlyGenerated`: that the description of such a circuit family is itself produced from the instance by a Cobham term. The circuits and their size bound are no longer assumed.

### Files

New: `Start/CobhamCircuit.lean` (compilation statement, base cases, composition), `Start/CobhamBRec.lean` (bounded recursion), `Start/PolyCircuit.lean` (application layer), building on the earlier `Start/CircuitBuild.lean` and `Start/WordCircuit.lean`. All are imported from `Start.lean`, build cleanly and produce no linter warnings. `Start/CookLevin.lean` keeps its original statements unchanged and gains the weaker-hypothesis versions. The task board (`docs/goal/task-board.yaml`), the evidence file `docs/goal/evidence/M9-COOK-LEVIN.md` and `docs/current-goal-state.md` were updated; `python3 scripts/goal_state.py validate` passes.

### What still remains

* **Cook–Levin: uniformity only.** The circuits are obtained by chaining existence lemmas, so no explicit function from instance to circuit is defined, and nothing yet says its Tseitin translation is the value of a Cobham term. Supplying that means turning the chain into an explicit compiler and writing the clause emitter as nested bounded recursions — a large further project. `NPHard Sat.SAT` is therefore still not proved outright.
* **M9-LAMBDAPI-LCCC** is unchanged; see the caveat below.

### Build caveat

The environment used here provided Lean 4.28 with a matching prebuilt Mathlib, while the project pins Lean/Mathlib 4.33. I temporarily retargeted `lean-toolchain` in order to build at all, and have **restored the project's own pin (`leanprover/lean4:v4.33.0`) and the original `lake-manifest.json`** in the final commit. Everything I wrote was checked under 4.28. Four pre-existing files depend on 4.33-only APIs and could not be compiled here — `Start/Lccc.lean`, `Start/CwaType.lean`, `Start/TM2Partrec.lean`, `Start/TM2Forward.lean` — so I left them untouched; this is why M9-LAMBDAPI-LCCC saw no work. Apart from those four (and a lint file in a dependency), the whole library builds with no errors, no `sorry`, and no warnings.

All work is committed and pushed.

# Summary of changes for run e27042b6-87c3-4bab-9995-71cbdee352aa
## What I did

Work continued on the last board item, `M9-COOK-LEVIN`. The whole project builds and contains no `sorry`; every new theorem depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**1. SAT is in NP — proved (`Start/Sat.lean`, new, imported by `Start.lean`).**
- CNFs (clauses of signed-index literals) and their truth value under an assignment word.
- An encoding of CNFs as binary words by a prefix-free token code read from the right (`1` = tick, `0 1` / `0 0 1` = negative / positive literal, `0 0 0` = clause separator), with a *total, junk-tolerant* decoder, so every word denotes a CNF; `decode_encCnf` proves decoding inverts encoding.
- `SAT` as a language of words, plus non-vacuity (`SAT_encCnf`, `SAT_encCnf_nil`, `not_SAT_encCnf_empty_clause`).
- An evaluator automaton that reads the token code while evaluating it against an assignment, proved to simulate the decoder, and its implementation as an explicit polynomial-time (Cobham) term by bounded recursion on notation (`eval_satMachine`), together with the verifier `satVerifier` and the witness-truncation lemmas that give the polynomial witness bound. Result: **`Complexity.Sat.inNP_SAT`**.
- Reusable polynomial-time gadgets (conditional, dropping `|u|` bits, iterated tail, bit access, Boolean combinators).

**2. Boolean circuits and the Tseitin translation — proved (`Start/Tseitin.lean`, new).** Straight-line circuits, their evaluator, circuit satisfiability, and the translation into CNF with one variable per gate and per input. Main results: **`csat_iff_sat_toCnf`** (the translation preserves satisfiability, both directions proved from the canonical assignment and from an arbitrary satisfying assignment) and `length_toCnf_le` (linear size).

**3. Cook–Levin, and the precise remaining gap (`Start/CookLevin.lean`, new).** NP-*hardness* of SAT is **not** proved. What is proved: the only missing ingredient is the compilation of an arbitrary polynomial-time verifier into a Boolean circuit family whose formula is emitted by a polynomial-time term. That statement is isolated as `Complexity.CircuitCompilable`, and from it **`npComplete_SAT_of_circuitCompilable`** (SAT is NP-complete) and `peqNP_iff_inP_SAT_of_circuitCompilable` follow, using the Tseitin translation. The hypothesis is never assumed — it occurs only as an antecedent. Unconditionally, `polyManyOne_SAT_of_inP` shows every language in P reduces to SAT.

Why hardness is not finished: because polynomial time for functions is defined syntactically (Cobham-style) rather than by machines, compiling a verifier means a structural recursion over the term (fixed-width value blocks with presence bits, unary multiplication for the smash function, unrolling of bounded recursion), and on top of that the formula emitter must itself be a polynomial-time term with unary index arithmetic. That is a very large development; rather than leave holes, the boundary is documented precisely and the conditional theorem makes the gap formal.

**4. Earlier work registered and documented.** The representation-invariance results for Kolmogorov complexity (exact equality of the de Bruijn and locally nameless measures, the identity `|bits t| = size t + nodes t`, and the proof that the factor two between the size and bit measures does *not* improve to an additive constant) are now recorded on the board as a completed item with its own evidence note.

**5. Project bookkeeping.** New evidence notes `docs/goal/evidence/M9-COOK-LEVIN.md` and `docs/goal/evidence/M9-KOLMOGOROV-REPRESENTATION.md`; the task board updated (`M9-COOK-LEVIN` now partial with an explicit open boundary, new item for the Kolmogorov work), re-rendered `docs/current-goal-state.md`, and the board validator passes. The README's overview and roadmap were updated to match. All work is committed and pushed.


# Summary of changes for run 930f128c-081a-4433-96b9-0c555584c431
Both remaining gaps are now closed, with everything building under `lake build` and no `sorry` anywhere in the `Start` library.

**1. Adequacy / 完备性 for Gödel's System T** (finished and verified from the previous session's work)

- `Start/SystemTConfluence.lean`: congruence and substitution lemmas for reduction, local confluence, Newman's lemma, confluence for typable terms, and uniqueness of numeral normal forms.
- `Start/SystemTDenot.lean`: a set-theoretic denotational semantics (`tyDen`, `Env`, typing derivations as data, `eval`, `denot`), a logical relation, and the headline results:
  - `adequacy` — a closed term of type `nat` reduces to the numeral of its denotation;
  - `denot_eq_iff_joins` — at base type, equal denotations ⟺ reduction to a common numeral;
  - `obsEq_of_denot_eq` and `denot_eq_iff_obsEq_nat` — equal denotations imply observational equivalence, and at base type the three notions coincide.
  - Boundary documented in the module docstring: full abstraction at higher types is not claimed, and `denot` evaluates a canonically chosen derivation (Curry-style typing is not unique), with irrelevance proved at base type.

**2. Curry–Howard–Lambek: STLC ⟺ CCC**

- `Start/Stlc.lean`: intrinsically typed simply typed lambda calculus with a unit type, binary products and function types; renamings, substitutions and their laws; βη-conversion (`Conv`) with compatibility under substitution.
- `Start/StlcCcc.lean`: the syntactic category (types as objects, one-variable terms modulo conversion as morphisms, substitution as composition) — `Stlc.category`; the unit type is terminal and the product type is a binary product, giving `Stlc.cartesianMonoidal`; the exponential functor and the currying bijection `Hom (X × Y) Z ≃ Hom Y (X ⇒ Z)` by β and η, whose naturality yields the adjunction `- ⊗ X ⊣ X ⇒ -` and hence `Stlc.monoidalClosed`. (In this Mathlib version "cartesian closed" is `CartesianMonoidalCategory` + `MonoidalClosed`; both instances are provided.)
- `Start/CccModel.lean`: the converse direction — types as objects and terms as morphisms in an arbitrary cartesian closed category, the substitution lemma (`tmMor_sub`: substitution is composition), soundness `tmMor_conv` (convertible terms have equal interpretations), and the resulting functor `interpFunctor` out of the syntactic category, together with lemmas showing it preserves the terminal object, products with projections and pairing, and the exponentials with currying. Boundary documented: strict freeness (uniqueness of the structure-preserving functor) is not claimed.

`#print axioms` on all headline results reports only `propext`, `Classical.choice`, `Quot.sound`.

Housekeeping: the three new modules are imported by `Start.lean`; `README.md` and the `Start/Demo.lean` guided tour were extended with the new results; two task-board entries (`M9-SYSTEMT-ADEQUACY`, `M9-STLC-CCC`) with evidence files were added, `python3 scripts/goal_state.py validate` passes (58 tasks) and `docs/current-goal-state.md` was regenerated. All changes are committed and pushed.

# Summary of changes for run 6b7e3b4f-9c55-4ff5-abc6-07bd07dae966
## What I did

I continued the denotational-semantics line of work and brought Scott's `D∞` construction to completion, sorry-free. The full library builds cleanly (`lake build`, 8806 jobs, **zero errors, zero warnings**), and `#print axioms` on every headline theorem reports only `propext, Classical.choice, Quot.sound`.

### New: the isomorphism `D∞ ≅ [D∞ →𝒄 D∞]` (`Start/ScottDinfIso.lean`)

Building on the tower `D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]`, its embedding–projection pairs, and the inverse limit (`Start/ScottTower.lean`, `Start/ScottDinf.lean`, `Start/ScottPsi.lean`), I constructed application `Φ : D∞ → [D∞ →𝒄 D∞]` as the supremum of its finite approximations and its inverse `Ψ`, and proved:

- `Phi_app_psi` — the computation rule for `Φ` on the image of the level embeddings;
- `Psi_Phi`, `Phi_Psi` — the two inversion laws;
- `dinfOrderIso : Dinf ≃o (Dinf →𝒄 Dinf)` — **Scott's theorem**, with `Phi_continuous`/`Psi_continuous` showing both directions are Scott continuous, so it is an isomorphism of ω-cpos;
- `dinf_nontrivial` — `D∞` has at least two elements, so the model is not degenerate.

### New: `D∞` as a model of the λ-calculus (`Start/ScottDinfModel.lean`)

The interpretation `ddenot` of de Bruijn terms in `D∞`, defined by plain structural recursion (abstraction is totalised, its continuity established afterwards), with:

- `ddenot_cont` — the interpretation is Scott continuous in the environment;
- `ddenot_lift`, `ddenot_subst`, `ddenot_beta` — lifting, substitution and the semantic β rule;
- `ddenot_step`, `ddenot_reduces`, `ddenot_conv` — soundness for β;
- `ddenot_eta` — **the η rule**, valid because `Φ` is an isomorphism and not merely a retraction. This is what the graph model of `Start/GraphModelSemantics.lean` cannot give, since it is not extensional.

### New: `⟦Ω⟧ = ⊥` and consistency of `λη` (`Start/ScottDinfOmega.lean`)

By computing the levels of `⟦λx. x x⟧` explicitly and inducting on the level, `ddenot_omega` shows the diverging term `Ω` denotes the least element, while `ddenot_I_ne_bot` shows `⟦I⟧` does not. I introduced `ConvBE`, the compatible equivalence relation generated by β-reduction *and* η-contraction (the project had no η-conversion relation before), proved the model sound for it (`ddenot_convBE`), and concluded `not_convBE_omega_I` / `convBE_consistent`: **the λη calculus is consistent**, by a purely semantic argument.

### Housekeeping

- All five new/previous `D∞` modules plus the two graph-model modules are now imported by `Start.lean`.
- Added task-board entries `M9-GRAPH-MODEL` and `M9-SCOTT-DINF` (both `DONE_STRONG`) with full evidence notes under `docs/goal/evidence/`; `python3 scripts/goal_state.py validate` passes (56 tasks) and `docs/current-goal-state.md` is re-rendered.
- Updated `README.md` (feature list and roadmap) and `Start/Demo.lean` (a new section with `#check`s of the headline statements).
- The earlier verification debt (`lake update` for `cslib` plus a full build) was already cleared and remains green.

### What is still open

`M9-COOK-LEVIN` remains the one `TODO_NEEDS_DESIGN` item on the board — no language is proved NP-complete. I did not start it: it needs an encoding of Boolean formulas as binary words, a polynomial-time evaluator inside the Cobham-style function class of `Start/ComplexityClasses.lean`, and a tableau construction, and I preferred to finish the `D∞` line completely rather than leave a partial Cook–Levin with holes. Nothing in the delivered project contains `sorry`.


# Summary of changes for run ead5e583-0a40-4924-9748-906547862a54
两项任务都推进了；任务 1 已完整完成，任务 2 完成了结构性理论层（Cook–Levin 未做，见下)。整个项目 `lake build` 通过（8798 jobs，无错误无 linter 警告），`Start/` 下没有任何 `sorry`。

## 1. 表示等价性:De Bruijn ⟺ locally-nameless ⟺ BLC(已完成)

新文件 `Start/Representation.lean`(已被 `Start.lean` 导入)。cslib 已作为 Lake 依赖(tag v4.33.0),桥接的是 `Cslib.LambdaCalculus.LocallyNameless.Untyped`。

- **翻译函数**:`Lambda.toLN` / `Lambda.ofLN`。采用 **de Bruijn levels** 的规范化翻译:自由索引直接解释为原子 `0,…,D-1`,不需要名字环境,并使原子 `D` 对任何在大小为 `D` 的上下文中读取的项都是规范新鲜的 —— 这正是能双向使用 cslib 那条余有限量化的 ξ 规则的关键。
- **互逆性与封闭项双射**:`ofLN_toLN`、`toLN_ofLN`、`closedEquiv : {t // freeMax t = 0} ≃ {M // M.LC ∧ M.fv = ∅}`,并配套 `lcAt_toLN`、`lc_toLN`、`fv_toLN`、`freeMax_ofLN`。
- **替换/归约保持**:`toLN_lift`、`toLN_subst`、`toLN_subst_zero`(de Bruijn 的 subst 恰是 cslib 的 opening)、`toLN_open_fvar`;单步正向模拟 `step_toLN` 与**反向反射** `reflect_step`,以及多步版 `reduces_toLN`、`reflect_reduces`。因为有反射,两侧归约是"同一个关系",不只是互相模拟。
- **合流双向互证**:`confluence_of_cslib : Lambda.Confluence`(由 cslib 的 `Term.confluent_fullBeta` 导出,是本库 `Lambda.confluence_theorem` 的独立证明)与 `cslib_confluence_of_lambda`(反向transport)。
- **三种表示**:与 `Start/BLC.lean` 的 `bitsEquiv` 复合得到 `closedBitsEquiv`。
- **note**:`docs/representations.md`("三种表示一致性"说明,含方法、关键引理与未做部分),证据文件 `docs/goal/evidence/M9-REPRESENTATION-BRIDGE.md`,任务板新增 M9-REPRESENTATION-BRIDGE,README 相应更新。
- 已验证公理只依赖 `propext, Classical.choice, Quot.sound`。
- 边界:只处理 β(不含 η、类型系统),原子类型固定为 ℕ,`cslib_confluence_of_lambda` 显式携带原子上界 `D`。

## 2. 复杂度理论(第 1–4 步完成;第 5–6 步 Cook–Levin/3SAT 等**未做**)

新文件 `Start/ComplexityClasses.lean`(已导入 `Start.lean`),语言取 `List Bool`。

- **多项式时间函数**按 **Cobham 公理**定义(`Cob` 语法 + `Cob.eval` 语义:空串、投影、两个后继、smash、复合、notation 上的有界递归)。这样"对复合封闭"是构造子而非定理,正是 P/NP/≤ₘᵖ 结构定理所需。证明了 `Cob.polyLen`:Cobham 函数输出长度被输入长度的多项式界住。为了说明这个类真的能用,证明了**串接可定义**:`Cob.eval_concat : concat.eval [x,y] = x ++ y`(用 smash 造出界 `1^{(|x|+1)(|y|+1)}`),另有 not/and/or/tail/headTrue 等小工具。
- **类与归约**:`InP`、`InNP`(证书式:多项式长度见证 + 验证器本身拒绝过长见证,这是使该类对归约封闭的标准规范化)、`PolyManyOne`(记号 `≤ₘᵖ`)、`NPHard`、`NPComplete`、`PeqNP`。
- **已证结构定理**:`inNP_of_inP`(P ⊆ NP)、`polyManyOne_refl/trans`、`InP.of_reduction`、`InNP.of_reduction`(此处用到多项式输出长度界与多项式复合)、`NPHard.of_reduction`、`peqNP_of_npComplete_of_inP` 与 `inP_of_peqNP`、`InP.compl/inter/union`、`InNP.union`、`bruteForce_decides`(NP 语言由显式穷举搜索判定)、非空性 `inP_univ/inP_empty/inP_nonempty`。
- **诚实的边界(已写进模块文档、证据文件与 README)**:Cook–Levin **未形式化**,没有任何语言被证明是 NP-完备的,因此 `NPHard` 未知是否非空,`PeqNP` 既未证明也未否证;Cobham 定理(Cobham 类 = 多项式时间图灵机可计算)未形式化;与 mathlib `Computable`/`Start/TM2PolyTime.lean` 之间没有建立联系。另外我刻意避免了"P 中语言可判定"这类命题——在 Lean 里 `Nonempty (DecidablePred L)` 对任意 `L` 经典地成立,那样的陈述是空洞的,所以改为给出显式的 `bruteForce` 函数。
- 证据文件 `docs/goal/evidence/M9-COMPLEXITY-CLASSES.md`,任务板新增 M9-COMPLEXITY-CLASSES(DONE_STRONG)与 M9-COOK-LEVIN(TODO_NEEDS_DESIGN,写明还缺什么);`docs/current-goal-state.md` 已重新生成,`scripts/goal_state.py validate` 通过(54 tasks)。
- 关于 mathlib 的 complexity theory PR 撞车风险:我无法在此环境访问 Zulip/GitHub 讨论,只能提示这一点仍需你自行确认。

## 需要你手动做的事(无法从这里完成)

`docs/RELEASING.md` 里列的 GitHub 侧操作:删除误建的 `v4.33.0` release 与 tag、创建 `v0.1.0`、设置仓库描述与 topics。

## 关于 README 开头那段署名

仓库源文件 `README.md` 里该段只出现在结尾的 "Provenance and status" 一节;你看到它出现在最开头,是因为交付时会自动在文件顶部再插入一次。源文件本身已按你的要求调整过了。


# Summary of changes for run 988d1de1-ccb4-4c96-b2a9-31b171749fd3
The project now builds cleanly on Lean/Mathlib **v4.33.0** and has been extended with one new result.

**1. The v4.33.0 migration you reported is complete.** All the errors and warnings in your build log are gone:
- `Turing.Reaches` / `Turing.eval` / `Turing.mem_eval` were renamed to `StateTransition.Reaches` / `StateTransition.eval` / `StateTransition.mem_eval` in `Start/TM2Forward.lean` and `Start/TM2Capstone.lean`.
- The residual goals in `Start/TM2Forward.lean` and `Start/TM2Partrec.lean` (places where `rw`/`simp` no longer close the goal by themselves) were discharged with explicit `rfl` / `change` / `exact` steps.
- `Turing.TM2Computable` and `TM2ComputableInPolyTime` now take raw encoding functions instead of the deprecated `Computability.FinEncoding`; `Start/TM2Partrec.lean` and `Start/TM2PolyTime.lean` were updated accordingly (including the `idComputable` example, which now uses `inferInstanceAs (Fintype _)`).
- Deprecations cleared: `push_neg` → `push Not` (`Start/BohmOut.lean`, `Start/BohmEta.lean`, `Start/OmegaUIncompressible.lean`), `Set.mem_setOf(_eq)` → `Set.mem_ofPred(_eq)`, and the unused-tactic line in `Start/KCComputable.lean`.
- `lean-toolchain` is `leanprover/lean4:v4.33.0` and `lakefile.toml` pins Mathlib to the matching tag.

A full `lake build` completes successfully (8782 jobs) with **no errors and no warnings**, and `Start/` contains no `sorry` and no `axiom`.

**2. New mathematics: the universal prefix machine is optimal for the lambda prefix machine.** New file `Start/KUOptimal.lean` (imported by `Start.lean`) connects the two prefix complexities of the library, which previously stood side by side:
- `KC.lamReq` turns the programs of the lambda prefix machine into a total computable stream of Kraft–Chaitin requests — the request `(|bits t|, m)` for each closed term `t` whose leftmost run reaches the Church numeral of `m`, issued exactly once (`KC.computable_lamReq`, `KC.exists_lamReq_of_isProgramFor`).
- `KC.sum_wtOpt_lamReq_le` bounds its total weight by one, via Kraft's inequality for the prefix-free coding `Lambda.bits`.
- `KC.exists_const_KU_le_kolmP : ∃ c, ∀ s, KU s ≤ Lambda.kolmP s + c` — optimality.
- `KC.exists_const_le_kolmP_prefix_of_exists_const_le_KU` transports `KU`-incompressibility of a sequence's prefixes to `Lambda.kolmP`.

All of these depend only on `propext`, `Classical.choice`, `Quot.sound`. Only this direction of the comparison is proved; the opposite bound is not expected to hold with these definitions (a lambda program spends two bits per syntax-tree node, while a `U`-program is an arbitrary bit string), and that boundary is written down explicitly rather than glossed over.

**3. Documentation and bookkeeping brought up to date.**
- `README.md`: headline-theorem block, content map, related-work table and roadmap all updated for the Levin–Schnorr theorem and the new optimality result; the roadmap row for Levin–Schnorr now states the precise remaining gap instead of an outdated claim. Badges updated to 51/51.
- `Start/Demo.lean`: `#check` added for the new theorem.
- Task board: new task `M8-KU-OPTIMAL` with evidence note `docs/goal/evidence/M8-KU-OPTIMAL.md`; the boundary paragraph of `docs/goal/evidence/M7-LEVIN-SCHNORR.md` corrected now that half of the `KU`/`kolmP` comparison exists. `python3 scripts/goal_state.py validate` reports "OK: 51 tasks validated" and `docs/current-goal-state.md` has been re-rendered.

The other roadmap directions (Cook–Levin/NP-completeness, Schnorr randomness and Solovay tests, Gentzen consistency and ordinal analysis, reverse mathematics, and bridges to other Lean libraries) remain **not implemented**; they are documented as open in the README roadmap table.

Everything is committed and pushed.

# Summary of changes for run cd54db65-c282-4bfc-b499-609368e066e5
Yes — the project is finished, and I re-verified it end to end in this session rather than taking the earlier report on trust.

**Verification performed now**
- `lake build` completes successfully (8100 jobs, no errors, no linter warnings) against the pinned toolchain and Mathlib.
- No `sorry` or `admit` anywhere in the library (`Start/` and `Start.lean`).
- Axiom check on headline results (`KC.mlRandom_omegaSeq`, `Lambda.separable_toTerm_of_not_tagEq`, `lambdaComputable_iff_computable`) reports only `propext`, `Classical.choice`, `Quot.sound`.
- The task board (`docs/goal/task-board.yaml`) validates: 49 tasks, all `DONE_STRONG`, with no open boundaries; `docs/current-goal-state.md` re-renders unchanged.

**One loose end found and cleaned up**
`Start/MLTestRequests.lean` was sitting inside the library directory but was not imported by `Start.lean` and did not compile on its own (several of its computability proofs exhausted the elaborator). It turned out to be a superseded first draft: the same construction — the passage from a Martin-Löf test to a Kraft–Chaitin request stream (`discovered`, `cutLength`, `covered`, `piece`, `testReq`, their computability, the total-weight bound, and `KC.mlRandom_omegaSeq`) — is carried out in full, and is proved, in `Start/OmegaURandom.lean`, which is part of the build. To leave the library tree unambiguous I moved the draft out of `Start/` to the top level alongside the other clearly-marked scratch files, added a header explaining what supersedes it and why it does not compile, and listed it (plus `Scratch.lean`) in the README's scratch-files section. No mathematical content was deleted, and nothing in the library depended on it.

All changes are committed and pushed.

# Summary of changes for run c18549c1-f7fd-42f8-aa68-ecfd602c7486
Continued and finished the last open item on the project's task board, `M7-BOHM-SEPARATION` (Böhm's separation theorem).

**What was already there at the start of this session:** finite Böhm trees and separation for a difference at the *root* of two trees (`Start/Bohm.lean`), plus an uncompiled draft of the "Böhm out" step in `Start/BohmOut.lean`.

**What I completed:**

1. `Start/BohmOut.lean` — verified and finished the Böhm-out transformation via *tagged tuples* `Gᵢ = λu₁ … u_K w. w u₁ … u_K ⟨i⟩`: a closed applicative context walks down both trees, and at the end the tag identifies the head while the number of stored arguments identifies the arity. Main results: `Lambda.separable_instTree` (the induction), `Lambda.separable_toTerm_of_bohmDiffer`, and `Lambda.separable_of_toTerm_ne` for trees with matching binder counts.

2. `Start/BohmEta.lean` (new) — removed the matching-binders restriction, which was the honest boundary left by the previous work. Each node is compared *after η-expansion to the common arity* `max b₁ b₂`, and variables are named by tags rather than de Bruijn indices, so subtrees on the two sides of an η-expansion can still be compared. This gives:
   - `Lambda.TagEq` (η-equality of Böhm trees) and `Lambda.TagDiffer` (its positive negation), proved complementary by `Lambda.tagDiffer_of_not_tagEq` and `Lambda.not_tagDiffer_of_tagEq`;
   - `Lambda.reduces_node_eta`, the η-general descent step, and `Lambda.separable_of_tagDiffer`, the η-general Böhm-out induction;
   - **`Lambda.separable_toTerm_of_not_tagEq`**: two closed normal forms whose Böhm trees are not η-equal are separable — one list of closed arguments sends the first term to `true` and the second to `false`.
   - Non-vacuity checks: `Lambda.separable_I_K` (a separation of `λz. z` from `λz w. z`, whose trees have different binder counts at the root, so it is out of reach of the earlier form), `Lambda.tagEq_refl`, and a worked example showing the trees of `λz. z` and `λz w. z w` are η-equal, hence not claimed separable (which is necessary: separation is stated via β-reduction to the exact terms `true`/`false`).

   Note on formalization: since the development has no term-level η-reduction relation, βη-equality of normal forms is rendered by the tree relation `TagEq` (node-wise comparison of the η-expanded trees).

3. Both modules are imported by `Start.lean`. Full `lake build` succeeds (8100 jobs), there is no `sorry` anywhere in `Start/`, no linter warnings, and the headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

4. Housekeeping: rewrote `docs/goal/evidence/M7-BOHM-SEPARATION.md`, flipped the task to `DONE_STRONG` with an empty open boundary in `docs/goal/task-board.yaml`, re-validated and re-rendered `docs/current-goal-state.md` (the whole board is now `DONE_STRONG`), and updated `README.md` and the `Start/Demo.lean` tour, which previously stated that Böhm's theorem was not proved. All work is committed and pushed.

# Summary of changes for run 588078ae-614e-4aac-ba13-49d740412991
Done — the dependency resolution is fixed and the project builds cleanly.

What I did:

1. **Ran `lake update`.** The checked-in `lake-manifest.json` had recorded all dependencies as local *path* packages pointing into `.lake/packages/…`, which is not part of the repository. On any fresh checkout that makes Lake re-resolve everything on every invocation. `lake update` regenerated the manifest with proper **git** dependencies, with Mathlib pinned to `v4.33.0` (rev `db584cd6d46c92f209a44c0f1c829460d327499d`), matching `lakefile.toml` (`rev = "v4.33.0"`) and `lean-toolchain` (`leanprover/lean4:v4.33.0`). The prebuilt Mathlib artifacts for that revision were fetched, so no from-source rebuild of Mathlib is needed.

2. **Full build verified:** `lake build` completes with `Build completed successfully (8760 jobs)` — no errors and, after the fix below, no warnings or stray "Try this" output.

3. **Fixed the one remaining linter warning** (`Start/OmegaUncomputable.lean`, `is_valid_code_pair_one`): the flexible-tactic linter flagged a `simp_all` followed by goal-modifying tactics. I replaced it with an explicit `simp_all only [...]` step (root fix, no linter suppression); the lemma and everything downstream still compile.

4. **Sanity checks:** no `sorry`/`admit` anywhere in `Start.lean` or `Start/` (the only matches are the words "admits"/"no sorry" inside documentation prose); the project's own `scripts/goal_state.py validate` passes (28 tasks) and reports the active milestone as complete; and representative theorems (`Lambda.chaitinOmega_mem_Ioo`, `Kraft.tsum_wt_le_one`, `Lambda.kraft_kolmP`) depend only on `propext, Classical.choice, Quot.sound`.

All changes (`lake-manifest.json`, `Start/OmegaUncomputable.lean`) are committed and pushed. `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run c9181d9b-da19-4b39-9ba4-21e5de947287
**问题定位：不是证明里的死循环，而是依赖解析导致的“永远编译不完”。**

仓库里 `lake-manifest.json` 记录的依赖类型是 **path（本地路径）**，指向 `.lake/packages/...`，而 `.lake/` 在 `.gitignore` 里并不入库。于是在任何干净的检出上：

- `lake` 每次都报 `manifest out of date: source kind (git/path) of dependency 'mathlib' changed`，重新解析依赖；
- 由于拿不到与 `lean-toolchain`（Lean v4.33.0）匹配的、已编译好的 Mathlib，它就从源码开始重编 Mathlib/Batteries/Aesop 等，几千个目标，编不完还报错，重跑又从头来 —— 表现就是“死循环”。

**已修复的内容**

1. `lake-manifest.json`：重新生成为 **git 依赖**，Mathlib 固定在 `v4.33.0`（rev `db584cd6d46c92f209a44c0f1c829460d327499d`），与 `lakefile.toml` 的 `rev = "v4.33.0"` 和 `lean-toolchain` 的 `leanprover/lean4:v4.33.0` 三者完全一致，`lake` 不再反复重新解析、不再重编 Mathlib。
2. `README.md`：新增 “Building” 一节，说明三处版本必须一致，以及从干净检出应先 `lake exe cache get` 再 `lake build`（这正是避免自行重编 Mathlib 的关键）。
3. `Start/OmegaUncomputable.lean`：清掉一处遗留的 `simp_all?`（改为 `simp_all`），它在每次构建时会打印四条 “Try this” 提示信息。

**验证**

- `lake build` 全量通过：`Build completed successfully (8760 jobs)`，无 error、无 warning、无 “Try this” 输出。
- `Start/` 及 `Start.lean` 中搜索 `sorry` / `admit`：没有任何遗留（`temp.lean`、`temp2.lean` 等 README 已标注的 scratch 文件不属于 `Start` 库、不参与构建，其中的 `sorry` 保持原样未动）。
- 代表性定理的公理依赖检查：`Lambda.chaitinOmega_mem_Ioo`、`Kraft.tsum_wt_le_one`、`Lambda.kraft_kolmP` 均只依赖 `propext, Classical.choice, Quot.sound`。
- `python3 scripts/goal_state.py validate` 通过（28 个任务），`next` 显示当前 milestone 已完成。

所有改动已提交并推送。若您指的“死循环”其实是别处（例如编辑器里某个文件卡住、或某条定义/证明本身循环），请告诉我具体文件与位置，我再针对性排查。


# Summary of changes for run 64ca70ab-9328-4d2a-84e2-29809a55a6e2
The project was not quite finished when I picked it up: 27 of the 28 board tasks were done, and one was still open — the prefix-free / Chaitin's Ω item. That item is now closed, so every task on the board is `DONE_STRONG`, the whole library builds, and there are no `sorry`s.

What I added (two new modules, both imported by `Start.lean`):

**`Start/Kraft.lean` — prefix-free codings and Kraft's inequality**
- `Kraft.wt w = 2 ^ (-|w|)`; `Kraft.PrefixFreeCoding c` (no code word is a prefix of another).
- `Kraft.boolLists`, `Kraft.ext` with their cardinalities, and the counting core `Kraft.sum_two_pow_sub_le`: extensions of distinct code words to a common length are disjoint.
- `Kraft.sum_wt_le_one` (finite form), `Kraft.summable_wt`, and `Kraft.tsum_wt_le_one`: `∑ 2 ^ (-|c i|) ≤ 1` for any prefix-free coding, plus `Kraft.tsum_wt_add_le_one`, which keeps the weight of an excluded code word in reserve.

**`Start/ChaitinOmega.lean` — self-delimiting coding, prefix complexity, Ω**
- `Lambda.bits`: the binary lambda calculus coding (`var i ↦ 1^(i+1) 0`, `lam t ↦ 00 t`, `app a b ↦ 01 a b`), proved self-delimiting (`bits_append_inj`), hence prefix free (`bits_prefixFree`) and injective.
- `Lambda.kolmP`: prefix complexity, the least *bit* length of a closed program for a number, with `kolmP_le_two_mul_kolm` relating it to the existing node-size complexity, and `Lambda.kraft_kolmP : ∑' s, 2 ^ (-kolmP s) ≤ 1` (shortest programs for distinct numbers are incomparable, by confluence).
- `Lambda.chaitinOmega`: the halting probability, the total weight of the closed terms with a normal form. `Lambda.summable_haltingWeight` shows the sum converges, `Lambda.chaitinOmega_le_one` is Kraft for the halting set, and `Lambda.chaitinOmega_mem_Ioo` gives `0 < Ω < 1` — positive because `I` halts, strictly below `1` because `omega` does not, so its own weight is left over.

Verification: `lake build` succeeds for the whole library; no `sorry` in the new files; `#print axioms` on `Lambda.chaitinOmega_mem_Ioo`, `Lambda.kraft_kolmP` and `Kraft.tsum_wt_le_one` reports only `propext`, `Classical.choice`, `Quot.sound`.

Bookkeeping done in the repository's own workflow: `docs/goal/task-board.yaml` now marks `M6-KOLMOGOROV-OMEGA` as `DONE_STRONG` with empty open boundary (`scripts/goal_state.py validate` passes, `next` reports the active milestone complete), a new evidence file `docs/goal/evidence/M6-KOLMOGOROV-OMEGA.md` records the claims and gates, `docs/current-goal-state.md` was regenerated, and the README and `Start/Demo.lean` showcase were updated. One honest boundary is recorded rather than glossed over: the algorithmic randomness of Ω (its incompressibility, and its first `n` bits deciding halting for programs of length `≤ n`) is not proved; only the definition, convergence, and `0 < Ω < 1` were required.

All work is committed and pushed.

# Summary of changes for run 20a75db6-a5d0-42cb-bbea-4a022a5d2041
我把 Kolmogorov 复杂度做成了新的里程碑 M6：先按项目规矩把它拆成任务写进任务板，然后把其中三条全部证完（机检、无 `sorry`）。

**任务板（`docs/goal/task-board.yaml`，`active_milestone` 改为 M6，`scripts/goal_state.py validate` 通过，28 条任务）**
- `M6-KOLMOGOROV-CORE`（DONE_STRONG）、`M6-KOLMOGOROV-BERRY`（DONE_STRONG）、`M6-KOLMOGOROV-INVARIANCE`（DONE_STRONG），各附证据文件 `docs/goal/evidence/M6-*.md`；
- `M6-KOLMOGOROV-OMEGA`（TODO_NEEDS_DESIGN）：Chaitin Ω 需要前缀无关编码，如实记录了开放边界与设计路线，未虚报完成。

**新模块 `Start/Kolmogorov.lean`（由 `Start.lean` 引入）**
- `Lambda.size`：项的语法规模（节点数，De Bruijn 下标 `i` 计 `i+1`）；`size (church n) = 3n+3`。
- `Lambda.kolm s = sInf { size t | t 闭且 t ↠ church s }`——`church s` 本身即程序，故集合非空、定义良基，`exists_program_of_kolm` 给出最短程序。
- **不可压缩数存在** `exists_incompressible : ∀ n, ∃ s, n ≤ kolm s`。计数论证：`finite_setOf_size_le`（规模 ≤ n 的项只有有限多个）加上合流性给出的 `unique_church_reduct`，得 `finite_setOf_kolm_le`。
- **K 不可计算**：`not_computablePred_kolm_le`（二元关系 `kolm s ≤ n` 不可判定）与推论 `not_computable_kolm`。这是 Berry 悖论走第二递归定理；为此在 `Start/SecondRecursion.lean` 补了闭项版不动点 `exists_code_fixed_point_closed`，并用 `size_le_encode : size t ≤ 2·encode t + 1` 完成规模核算（无需把项规模在码上做成可计算函数）。注意：对固定的 n，`{s | kolm s ≤ n}` 有限因而可判定，所以不可判定的只能是、也确实是那个一致的二元关系——这一点在文档里说明了，与最初按 Rice 定理的设想不同。
- **不变性**：`kolmWith U s`（以任意闭项 `U` 作解释器）满足 `kolm s ≤ kolmWith U s + size U + 1`，恒等解释器给回 `kolm` 本身（差常数 3）；`exists_const_kolm_le_of_partrec`：任意部分递归描述系统 `V` 有常数 `c` 使 `V p = s ⟹ kolm s ≤ 3p + c`；经模型等价得图灵机版 `exists_const_kolm_le_of_tm2`。

**新模块 `Start/KolmogorovBinary.lean`**：紧凑（二进制）数码 `Lambda.binNum n`——规模 `O(log n)` 的闭项且 `↠ church n`（用 `mult (church 2)` 与 `succ` 沿二进制展开构造，附闭性、正确性与规模界）。由此得对数形式的不变性：`exists_const_kolm_le_size`、`exists_const_kolm_le_size_of_partrec`、`exists_const_kolm_le_size_of_tm2`（`kolm s ≤ c·(p 的比特长度 + 1)`）。

**诚实边界**（写在文件头、README、证据文件与 `docs/church-turing-discussion.md` 新增第十三节）：加性不变性成立于"节点数"这个尺度；换成比特长度只得到常数倍界，因为每个比特要花常数个节点。按比特计长的加性陈述需要以比特计长的程序尺度，前缀复杂度与 Ω 还额外需要自定界（前缀无关）编码——现有编码是单射但非前缀无关，这条留作 `M6-KOLMOGOROV-OMEGA`。

**验证**：`lake build` 全量成功（8072 个任务），零错误、零 linter 警告；`Start.lean` 与 `Start/` 下无 `sorry`/`admit`；`#print axioms` 对本次所有主结果只报 `propext, Classical.choice, Quot.sound`。`README.md`、`Start/Demo.lean` 导览、`docs/current-goal-state.md` 均已更新；`ARISTOTLE_SUMMARY.md` 未改动。全部改动已提交并推送，工作区干净。

# Summary of changes for run 42c874b0-61ec-4c4f-8aa2-c490b993e78f
The five "possible next directions" from the notes and the README were added to the task board as milestone `M5` and are now all completed, machine-checked and documented.

**New Lean modules (all `sorry`-free, all imported from `Start.lean`)**

- `Start/RecursionParams.lean` — Kleene's recursion theorem **with parameters**: `Lambda.exists_recursion_with_parameters`, giving a primitive recursive `s` with `decode (s y) = some X` and `X ↠ F ⌜s y⌝ ⌜y⌝`.
- `Start/Encodings.lean` — model equivalence beyond unary functions: `lambdaComputable2_iff_partrec₂`, `lambdaComputable2_iff_tm2Computable`, and, for arbitrary `Primcodable` input/output types, `LambdaComputableEnc` / `TM2ComputableEnc` with `lambdaComputableEnc_iff_partrec`, `tm2ComputableEnc_iff_partrec`, `lambdaComputableEnc_iff_tm2ComputableEnc`. The compiler in `Start/PartialCapstone.lean` was strengthened to produce a **closed** term (`lambdaComputable_of_partrec_closed`).
- `Start/TM2PolyTime.lean` — time-bounded machine runs (`HaltsWithin`, `TM2ComputableNatInTime`, `TM2ComputableNatInPolyTime`), `lambdaComputable_of_tm2ComputableNatInPolyTime`, and bridges to Mathlib's `Turing.TM2ComputableInPolyTime`. Non-vacuity is witnessed by an explicit halting machine.
- `Start/Solvability.lean` — `Lambda.Solvable`, its conversion-invariance, `Lambda.not_solvable_omega`, generic reachability `Lambda.exists_args_conv_of_solvable`, and undecidability (`not_decides_solvable`, `not_computablePred_codeSet_solvable`).
- `Start/AlgorithmRepresentation.lean` — a Dershowitz–Gurevich style **representation theorem**: sequential algorithms in bounded-exploration form (`SeqAlgorithm.Algorithm`) have partial recursive input–output functions (`Algorithm.partrec_run`), hence lambda-definable and Turing-machine computable ones. Computability of the transition is *derived* (`primrec_stepProg`), not assumed; `run_doubling` shows a genuinely looping instance computing `n ↦ 2n`.

**Honest scope limits** (stated in the files and the notes): Böhm's separation theorem itself is not proved — only solvability, its undecidability and generic reachability. The algorithm result is a representation theorem for the stated axioms, not a proof of the Church–Turing thesis, which is not a formalizable statement. On the complexity side only the direction *out of* polynomial-time machines is formalized; no resource-preserving compilation into machines and no lambda-side cost model.

**Verification**: full `lake build` succeeds (8070 jobs) with no errors and no linter warnings; `Start.Demo` builds too. No `sorry`/`admit` anywhere in `Start.lean` or `Start/` (only prose mentions). Axiom audits on the headline results report only `propext, Classical.choice, Quot.sound` (`Lambda.not_solvable_omega` uses only `propext`).

**Documentation/bookkeeping**: `docs/goal/task-board.yaml` gained milestone `M5` with five tasks, all `DONE_STRONG` and each backed by an evidence note in `docs/goal/evidence/`; `scripts/goal_state.py validate` reports "OK: 24 tasks validated". `README.md` now lists the new modules and results and has a revised "Suggested Next Steps"; `Start/Demo.lean` has a new guided-tour section; `docs/church-turing-discussion.md` gained a section 十二 covering all five items with their limits, and its earlier "still to do" entry for the representation theorem is marked done. `docs/current-goal-state.md` was re-rendered. Everything is committed and pushed.

# Summary of changes for run 0d5efeda-0d94-45b1-b5a4-ee93b4cc7d80
Correct — there are no open tasks left, and I re-verified that this session rather than taking it on trust.

**Verification run just now**
- `lake build` completes successfully (8065 jobs), with no errors and no linter warnings.
- No `sorry`/`admit` anywhere in `Start.lean` or under `Start/` (the only textual matches are prose in comments/documentation such as `Start/Demo.lean`).
- The task board validates: `scripts/goal_state.py validate` reports "OK: 19 tasks validated", and `next` reports the active milestone M4 as complete, with every task done and no open boundaries.
- The working tree is clean and everything is committed and pushed; no code changes were needed.

**What the library currently contains** (all machine-checked, sorry-free): the model-equivalence theorems — lambda-definable ⇔ partial recursive (`lambdaComputable_iff_partrec`), Turing-machine-computable ⇔ partial recursive (`TM2Partrec.tm2Computable_iff_partrec`), and the two models agreeing (`lambdaComputable_iff_tm2Computable`) — together with the supporting metatheory (confluence, standardization, Gross–Knuth normalization and the arithmetized evaluator, minimisation and its divergence half) and the computability-theory layer built on top: the Turing fixed-point combinator, Kleene's second recursion theorem, undecidability of convergence and of normalizability, Scott's theorem and the lambda-calculus Rice theorem, the uniform s-m-n theorem, and a lambda-level self-interpreter (with the proof that the converse, quoting, is not lambda-definable).

**If you would like to keep going**, the natural remaining directions — none of them required by anything already proved — are:
1. A Dershowitz–Gurevich style representation theorem (axioms for "algorithm" ⇒ Turing simulability). This is the one item the notes deliberately left undone; it is a large piece of work, and even finished it would be a representation theorem, not a proof of the Church–Turing thesis, which is not a formalizable statement.
2. Further separation/solvability theory on top of the self-interpreter (e.g. Böhm's theorem, genericity of unsolvable terms).
3. More classical recursion theory transported into the lambda setting: the recursion theorem with parameters, Rogers' isomorphism theorem, or simple/creative sets.

Just tell me which, if any, you'd like next.

# Summary of changes for run ca9f651f-13c2-476b-8145-22b2bced9f7b
I picked the project up where it stood, re-verified it end to end, and closed out the one item its own notes still listed as open — a lambda-level self-interpreter.

**Re-verification of the existing development**
- `lake build` succeeds from a clean rebuild of the library: no errors and no linter warnings.
- No `sorry`/`admit` anywhere in `Start.lean` or under `Start/` (the only textual matches are prose in comments).
- The task board validates and every task is complete.

**New mathematics proved this session** (`Start/SelfInterpreter.lean`, imported by `Start.lean`, no `sorry`; `#print axioms` on each headline result reports only `propext`, `Classical.choice`, `Quot.sound`)
- `Lambda.exists_self_interpreter` — there is a single **closed** term `E` such that for every closed term `M`, `E (church (encode M))` **reduces** to `M` (a reduction, not merely beta conversion). Previously the repository's evaluator `Lambda.eval_gk` worked only on codes: code in, code of the normal form out. This is the code-to-term statement.
- `Lambda.selfEval_correct` — the general form: the interpreter, run on the code of an arbitrary (possibly open) term `t` in an environment term realizing a family `u`, reduces to the parallel substitution `Lambda.substEnv u t`. The abstraction case reduces under the binder, which is why the environment formulation is needed.
- `Lambda.not_exists_quote` — the exact converse fails: no term `Q` satisfies `Q M ↠ church (encode M)` for all closed `M`. Interpreting (code → term) is lambda-definable; quoting (term → code) is not. Proved from confluence, using that `I` and `I I` share a reduct but have different codes.
- `Lambda.exists_self_interpreter_church` — a non-vacuity check: on the code of `church k` the interpreter returns `church k`.

The construction is the environment-passing interpreter knotted with Turing's fixed-point combinator `Lambda.Theta`; the numeric destructors of the encoding are computable, so the existing realizer compiler supplies the closed terms it needs — no new assumption is introduced. Supporting theory added along the way and reusable elsewhere: `Lambda.substEnv`/`Lambda.envCons` (parallel substitution and its congruence lemmas), `Lambda.freeBelow` with the previously missing inversion of the substitution-based closedness predicate, and `Lambda.reduces_lift` (reduction is preserved by lifting).

**Documentation** — `README.md`, `Start/Demo.lean` (guided tour), `docs/church-turing-discussion.md` (new section, and the earlier "still to do" note updated), the task board with a new completed task, and the evidence note `docs/goal/evidence/M4-SELF-INTERPRETER.md`. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed; the working tree is clean.

One item recorded on the board's wish-list remains deliberately undone: formalizing a Dershowitz–Gurevich style representation theorem. As the discussion document argues, even completed it would be a representation theorem, not a proof of the Church–Turing thesis, which is not a formalizable statement.

# Summary of changes for run 490e1577-7f95-4cf4-a5ec-f1f6d464db16
我把上一轮回答末尾"下一步建议"里的条目提炼成了可执行任务，并完成了其中两条（第三条说明见下）。

**任务一：Scott–Rice 定理（新文件 `Start/Scott.lean`）**

- `Lambda.Conv`：可转换性，定义为"有公共归约式"（由已证的 Church–Rosser 定理，它就是 β 等价）；配套证明了自反、对称、传递。
- `Lambda.ConvInvariant`：项类对可转换性封闭（"语义性质"）。
- `Lambda.Decides F A`：闭项 `F` 判定项类 `A`——`F ⌜X⌝ ↠ true`（当 `X ∈ A`）、`↠ false`（当 `X ∉ A`）。
- `Lambda.scott_theorem`（**Scott 定理**）：若 `A` 对可转换性封闭，且有一个闭项属于 `A`、另一个闭项不属于 `A`，则没有任何闭 λ 项判定 `A`。证明用对角项 `λc. if F c then N else M` 加上仓库已有的 Kleene 第二递归定理。
- `Lambda.not_computablePred_codeSet`（**λ 演算版 Rice 定理**）：同样条件下，`A` 中各项的编码集不是可计算谓词；中间步骤 `Lambda.exists_decider_of_computablePred` 把可计算的特征函数变成闭 λ 判定子。
- 非平凡实例（保证命题不空洞）：`Lambda.not_decides_conv_church_zero` 与 `Lambda.not_computablePred_codeSet_conv_church_zero`——"是否与 `church 0` 可转换"既不可 λ 判定也不可计算判定，见证项为 `church 0` 与 `omega`。

值得更正的一点：上一轮说 Scott–Rice 还缺一个 λ 层面的自解释器 `E ⌜X⌝ ↠ X`。实际不需要——只用第二递归定理即可对角化。自解释器仍然是有价值的后续工作（更精细的分离理论），但它不是 Scott–Rice 的前提；README 与讨论文档已按此更正。

**任务二：一致（uniform）s-m-n 定理（新文件 `Start/SMN.lean`）**

- `Lambda.smnCode`、`Lambda.smnCode_primrec`、`Lambda.exists_smn`：存在原始递归的 `s`，使 `s ⌜F⌝ n` 恰为 `F (church n)` 的编码；`Lambda.smn_realizes` 给出其归约层面的形式。此前该事实散落在各处的归约论证里，现在是一条可复用定理。

**任务三（未做，已如实记录）**：Dershowitz–Gurevich 风格的表示定理形式化，工作量最大，且即便完成也仍然只是表示定理、不是 Church–Turing 论题的证明。

**验证**：`lake build` 全量成功（8064 个任务），零错误、零 linter 警告；`Start.lean` 与 `Start/` 下无 `sorry`/`admit`；`#print axioms` 对 `Lambda.scott_theorem`、`Lambda.not_computablePred_codeSet`、`Lambda.not_decides_conv_church_zero`、`Lambda.not_computablePred_codeSet_conv_church_zero`、`Lambda.exists_smn` 均只报 `propext, Classical.choice, Quot.sound`。

**文档**：更新了 `README.md`（结果清单与后续方向）、`docs/church-turing-discussion.md`（新增第十节，并把已完成项划掉）、`Start/Demo.lean` 导览新增一节，任务板 `docs/goal/task-board.yaml` 增加两条 `DONE_STRONG` 任务并附证据文件 `docs/goal/evidence/M4-SCOTT-RICE.md`、`docs/goal/evidence/M4-SMN-UNIFORM.md`；`scripts/goal_state.py validate` 通过（18 条任务）。`ARISTOTLE_SUMMARY.md` 未改动，所有改动均已提交并推送。

# Summary of changes for run 7d763506-50e9-46c0-be50-e3438f97f409
## 我的看法（完整版写在 `docs/church-turing-discussion.md`）

**总体我同意你的三分法。** 补充与修正五点：

1. **最该守住的区分**：日常讨论把两件事混在一起——(a) 模型等价定理（λ 可定义 = 部分递归 = 图灵可计算），这是纯数学、可机检；(b) 论题本身（非形式的"有效可计算" = 这个类），一侧非形式，所以它不是"未证的定理"，而是**不可形式化的**。(a) 再多也不给 (b) 增加逻辑分量，只增加认识论分量。

2. **现代公理化的数学身份是"表示定理"**：「满足某组公理的对象可被图灵机模拟」。这类定理没有缺陷，缺的不是证明而是**充分性判断**（公理是否抓住了"算法"）——而充分性判断在数学里从来只被接受、不被证明。所以我不倾向把它叫"循环"。

3. **"自明"这个要求本身被过度苛求了**：我们从不要求 ε–δ、可测、紧致的定义自明，只要求稳定、有产出、与判例吻合。若用同一标准，CT 早已结案；它仍叫"论题"更多是历史与期待造成的。

4. **稳健性论证要打个折、也要加个码**：标准模型多出自同一批直觉，重合力度有限；真正有分量的是动机与"计算"无关的入口仍落进同一类——Diophantine 集 = r.e. 集（MRDP）、群论字问题、Post 对应问题、tag 系统/元胞自动机的普适性、一阶可证性的枚举。

5. **两处我会更保守**：物理 CT 与数学 CT 要分家（相对论计算冲击的是前者）；公理的争议性影响的是"定理覆盖多少种算法概念"，而不是"算法可能超出图灵可计算"。

**结论**：CT 论题不需要、也无法在 Lean 中被证明——任何"证明"都会把非形式的一侧换成形式定义，于是证的是表示定理，而"替换是否忠实"重新成为论题。值得形式化的是它周围的数学。

## 关于"还需要证什么"——本次实际补上的四条（全部机检、无 `sorry`，仅依赖 `propext, Classical.choice, Quot.sound`）

- `Lambda.Theta_reduces`（`Start/FixedPoint.lean`）：Turing 不动点组合子 `Θ = A A`，且 `Θ F` **归约到**（不只是 β 等价于）`F (Θ F)`；推论 `Lambda.exists_fixed_point`。此前仓库里没有任何不动点组合子。
- `Lambda.exists_code_fixed_point`（`Start/SecondRecursion.lean`）：**Kleene 第二递归定理的 λ 版本**——任意闭项 `F` 存在 `X` 使 `X ↠ F ⌜X⌝`，`⌜X⌝` 为 `X` 自身编码的 Church 数码。只需一个实现子（对角函数 `c ↦ app_code c (church_code c)` 原始递归）。
- `Lambda.not_computablePred_codeConverges`（`Start/Undecidable.lean`）：**λ 演算版停机问题不可判定**——没有可计算谓词判定"编码给出的项是否归约到某个 Church 数码"。由万有部分递归函数经 `lambdaComputable_of_partrec` 归约到 Mathlib 的停机问题。
- `Lambda.not_computablePred_codeHasNormalForm`（`Start/NormalizationUndecidable.lean`）：更强、也更标准的 **"是否存在范式不可判定"**；关键是发散时严格实现子连弱头范式都没有。配套的可复用引理 `Lambda.exists_strict_realizer`。

每条都附了非平凡性检查（Church 数码收敛/有范式，`omega` 不收敛/无范式），避免命题空洞。

**下一步建议**（写在 README 与讨论文档里）：Scott–Rice 定理还差一个 **λ 层面的自解释器**（`E ⌜X⌝ ↠ X`）——现有的 `eval_gk` 只在码层面工作；其次是编码下的一致（uniform）s-m-n；最后才是形式化一条 Dershowitz–Gurevich 风格的表示定理，但即使做完，那仍是表示定理，不是 CT 的证明。

## 验证

`lake build` 全量成功（8062 个任务），零错误、零 linter 警告；`Start.lean` 与 `Start/` 下无 `sorry`/`admit`（仅注释中的散文提及）；新定理的公理审计如上。原有内容未删改，`ARISTOTLE_SUMMARY.md` 未改动。所有改动已提交并推送。


# Summary of changes for run 302e2be8-5283-4b6a-8871-293651da9e41
Short answer: no — the Church–Turing thesis itself was not proved, and it cannot be, because it is not a mathematical statement. It asserts that the informal notion of "effectively calculable by a mechanical procedure" coincides with a formal notion of computability; one side of that identification is informal, so there is nothing to prove formally.

What this project does prove (all machine-checked, no `sorry`, depending only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`) are the *formal equivalences* between models of computation that are the mathematical content usually cited in support of the thesis:

- `lambdaComputable_iff_partrec` (`Start/PartialCapstone.lean`): a partial function on ℕ is lambda-definable exactly when it is partial recursive — for arbitrary partial functions, not just total ones. The divergence direction rests on `Lambda.muDivergence` (`Start/Divergence.lean`).
- `TM2Partrec.tm2Computable_iff_partrec` (`Start/TM2Capstone.lean`): a partial function on ℕ is computed by a bundled Turing machine (finite stack alphabets, computable input/output translations) exactly when it is partial recursive.
- `lambdaComputable_iff_tm2Computable` (`Start/TM2Capstone.lean`): the lambda-calculus and Turing-machine models formalized here agree.
- `lambdaComputable_iff_computable` (`Start/PartrecLambda.lean`): the corresponding statement for total functions.

Supporting theory, also fully proved: confluence (`Lambda.confluence_theorem`), Gross–Knuth normalization and correctness of the arithmetized evaluator, standardization (`Lambda.sred_of_reduces`), normalization of the weak head strategy, and correctness of the minimisation combinator.

So the docstring phrase "Church–Turing for the lambda calculus" on `lambdaComputable_iff_partrec` should be read as the model-equivalence theorem (lambda-definable ⇔ partial recursive), not as a proof of the thesis in its philosophical form.

Verification performed this session: `lake build` completes successfully (8058 jobs) with no errors; a search finds no `sorry`/`admit` in `Start.lean` or anywhere under `Start/` (the only textual matches are prose in `Start/Demo.lean`); the axiom audit above was re-run on the three headline theorems. No code changes were required, and the working tree is clean with everything already committed.

# Summary of changes for run a9f452c4-50c4-421b-bf82-fe17ee5ff34c
Yes — the project is finished, and I re-verified it end to end this session rather than taking the previous state on trust.

**Verification performed**
- `lake build` completes successfully (8058 jobs) with no errors and no linter warnings.
- A search for `sorry`/`admit` across `Start.lean` and the whole `Start/` library returns no occurrences (the only textual matches are prose in comments/documentation). The sorry-bearing files under `scratch/` are earlier exploratory drafts, are not part of the build target, and nothing in the library depends on them.
- Axiom audit on the headline theorems (`lambdaComputable_iff_tm2Computable`, `TM2Partrec.tm2Computable_iff_partrec`, `lambdaComputable_iff_partrec`, `Lambda.muDivergence`, `Lambda.confluence_theorem`, `Lambda.sred_of_reduces`): each depends only on `propext`, `Classical.choice`, `Quot.sound`.
- The task board (`docs/goal/task-board.yaml`) validates with all 16 tasks `DONE_STRONG` and every `open_boundary` empty; the active milestone reports as complete.

**What the library establishes**
- `lambdaComputable_iff_partrec` — a partial function on ℕ is lambda-definable exactly when it is partial recursive (arbitrary partial functions, not just total ones), resting on the divergence half of minimisation `Lambda.muDivergence`.
- `TM2Partrec.tm2Computable_iff_partrec` — a partial function on ℕ is computable by a bundled Turing machine (finite stack alphabets, computable input/output translations) exactly when it is partial recursive.
- `lambdaComputable_iff_tm2Computable` — the two models of computation agree.
- Supporting theory, all proved: confluence, Gross–Knuth normalization and correctness of the arithmetized evaluator, standardization, normalization of the weak head strategy, and correctness of the minimisation combinator.

No code changes were needed. The working tree is clean and the commit is already pushed; `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 1b47bb94-e317-4d47-8f33-be3956cdd130
The project is finished: the whole task board is closed and the Lean library builds clean, sorry-free and warning-free.

**Final verification**
- `lake build` → "Build completed successfully (8058 jobs)", no errors and no linter warnings.
- No `sorry`/`admit` anywhere in `Start.lean` or `Start/` (the only textual matches are prose in `Start/Demo.lean`).
- Axiom check on the headline theorems (`lambdaComputable_iff_tm2Computable`, `TM2Partrec.tm2Computable_iff_partrec`, `lambdaComputable_iff_partrec`, `Lambda.muDivergence`, `Lambda.confluence_theorem`, `Lambda.sred_of_reduces`) → only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/goal_state.py validate` → "OK: 16 tasks validated"; `next` → the active milestone M4 is `DONE_STRONG`. All 16 board tasks are `DONE_STRONG` with empty `open_boundary`.

**Headline results in the library**
- `lambdaComputable_iff_partrec` (`Start/PartialCapstone.lean`) — a partial function on ℕ is lambda-definable exactly when it is partial recursive; this covers arbitrary partial functions, not just total ones, and rests on `Lambda.muDivergence` (`Start/Divergence.lean`) for the divergence half of minimisation.
- `TM2Partrec.tm2Computable_iff_partrec` (`Start/TM2Capstone.lean`) — a partial function on ℕ is computable by a bundled Turing machine (with finite stack alphabets and computable input/output translations) exactly when it is partial recursive. The forward direction bundles the compiler from partial recursive functions into machines, restricted to the finitely many labels it uses (`Start/TM2Restrict.lean`, `Start/TM2Forward.lean`); the converse arithmetizes an arbitrary bundled machine (`Start/TM2Partrec.lean`).
- `lambdaComputable_iff_tm2Computable` (`Start/TM2Capstone.lean`) — the two models of computation formalized here agree.
- Supporting theory, all proved: confluence (`Lambda.confluence_theorem`), Gross–Knuth normalization and the correctness of the arithmetized evaluator, standardization (`Lambda.sred_of_reduces`) and normalization of the weak head strategy, and correctness of the minimisation combinator.

**Documentation**
`docs/goal/task-board.yaml`, `docs/current-goal-state.md`, the evidence notes under `docs/goal/evidence/`, `README.md` and `Start/Demo.lean` all reflect the final state. `ARISTOTLE_SUMMARY.md` was left untouched.

This session's work consisted of final verification and a small cosmetic pass; all changes are committed and pushed (`git status` clean, remote up to date).

# Summary of changes for run b02ab25d-5677-4432-83fc-eab0a035f776
I picked up the lambda-calculus formalization where it stood and closed out the remaining work on its task board. Everything is committed and pushed; a from-scratch rebuild (`rm -rf .lake/build && lake build`) succeeds with **zero** errors and zero linter warnings, and the library under `Start/` contains no `sorry`.

**New mathematics proved this session**

- `Start/Minimization.lean` was broken (its induction did not elaborate) and was not part of the library at all. I repaired it and wired it into `Start`, so the correctness of the minimisation combinator, `Lambda.muCorrectness`, is now a real, built theorem: if a closed term computes `f` on Church numerals and `n` is the least zero of `f`, then `mu F` reduces to `church n`.
- `Start/PartrecLambda.lean` (new) proves the reverse direction of the Church–Turing correspondence for the lambda calculus:
  - `Lambda.Realizes.muParam` — parameterised minimisation: `muParam H` realizes the least-witness function;
  - Kleene's normal form arithmetised (`Lambda.kleeneTest`, `Lambda.kleeneValue`, primitive recursive; witness existence and value extraction);
  - `Lambda.exists_realizer_of_computable` — every total computable function has a closed lambda realizer;
  - `lambdaComputable_of_computable`, and the capstone `lambdaComputable_iff_computable : LambdaComputable (fun n => Part.some (f n)) ↔ Computable f`.
- `Start/EvalGK.lean` now states and proves `Lambda.evalNormalizationGK`: the arithmetized Gross–Knuth evaluator returns the code of the normal form on every normalizing input (not just for Church numerals), which is what makes the bridge `LambdaComputable f → Partrec f` hypothesis-free.
- `Start/Minimization.lean` also adds the analysis of a witnessless search (`Lambda.muX_loop_step`, `Lambda.muX_loop`, `Lambda.mu_reduces_state`, `Lambda.muX_state_reduces_of_mu_reduces`).

`#print axioms` on all headline results reports only `propext`, `Classical.choice`, `Quot.sound`.

**Quality and housekeeping**

- Cleared the 17 linter warnings that had crept back in (non-terminal `simp_all` → explicit `simp_all only [...]`, goal-changing `show` → `change`, long lines, one unused simp argument). No linter was disabled and no `nolint` added.
- Moved the four scratch experiment files (which still contain `sorry`s and are not part of the build) into `scratch/` with a README, so the library tree is unambiguous.
- Updated `README.md`, `Start/Demo.lean` (guided tour now covers the reverse direction and the equivalence), the task board and `docs/current-goal-state.md`, and wrote the evidence notes for each task now complete.

**What is honestly still open** (both recorded on the board with precise boundaries)

- The *divergence* half of minimisation — if the tested function has no zero, `mu F` should reduce to no Church numeral. `Lambda.muX_state_reduces_of_mu_reduces` pins down why this cannot be closed with the present theory: a constant function satisfies every reduction equation of the loop, so head normal forms (solvability) plus a standardization theorem are needed. This is also what would discharge `Lambda.EvalNormalization` for the leftmost evaluator, and it is the only reason the capstone equivalence is stated for total rather than arbitrary partial functions.
- `M4-TM2-IMP-PARTREC` (TM2-computable implies partial recursive), a self-contained development of its own size that nothing else in the repository depends on; the evidence note sketches the intended design.


# Summary of changes for run 0f8f5102-6e41-4ea8-a3b0-cb9b72087b69
Both requested task-board items are finished, and the whole tree is committed and pushed.

**M2-EVAL-CORRECTNESS-DISCHARGE (P1) — done**

Evaluator correctness is no longer assumed. The previously assumed hypothesis `Lambda.EvalCorrectness` is in fact false (`Lambda.not_evalCorrectness`), so instead a Gross–Knuth (complete-development) evaluator was built and proved correct outright:

- `Start/GrossKnuth.lean`: the normalization result `Lambda.rho_iterate_eq_of_reduces_normal` — if a term reduces to a normal form, finitely many iterations of the complete development reach it exactly.
- `Start/EvalGK.lean`: the arithmetized evaluator `Lambda.eval_gk`, its partial-recursiveness, soundness and completeness, the correctness statement `Lambda.evalCorrectnessGK`, and the unconditional bridge `LambdaComputable_imp_Partrec_unconditional : LambdaComputable f → Partrec f`.

Evidence is in `docs/goal/evidence/M2-EVAL-CORRECTNESS-DISCHARGE.md`.

**M2-STYLE-RESIDUE (P2) — done**

The three residual linter classes are now completely empty; `lake build` emits no `linter.*` warning at all (down from 89 `style.longLine`, 83 `flexible`, 57 `style.multiGoal` as recorded on the board). No linter was disabled and no `nolint`/`set_option linter.* false` was added.

- `flexible`: every non-terminal `simp`/`simp_all` was replaced by the explicit `simp only [...]` / `simp_all only [...]` set it actually used.
- `multiGoal`: multi-goal tactic sequences were focused with `·` bullets or replaced by single `exact`/`refine` terms. Notably `Lambda.unpairLeft_step2` and `Lambda.unpairRight_step2` are now direct congruence proofs; `LambdaComputable2.mult` and `LambdaComputable.pred` use `use` for the witness; `Lambda.lift_ecf_primrec`, `Lambda.subst_ecf_primrec` and `Lambda.subst_code_primrec` are single applications of `Primrec.nat_strong_rec`; `Lambda.subst_code_case1_primrec` states its helper before `Primrec.of_eq`; `Lambda.code_step'_sound_var` now rewrites with a named `have` instead of an `aesop`-driven script.
- `longLine`: long declarations, comments and proof terms reflowed at 100 columns, with several inline `match` expressions rewritten in multi-line form.
- One reusable lemma was added: `Lambda.reduces_app` in `Start/Reduction.lean` (congruence of `Lambda.reduces` for applications in both arguments).

Evidence is in `docs/goal/evidence/M2-STYLE-RESIDUE.md`.

**Verification**

- `lake build` succeeds; a scan of the full build log finds zero `linter.*` warnings (the only remaining messages are the pre-existing `aesop: failed to prove the goal` notices, which are not part of these classes).
- No `sorry`/`admit` anywhere under `Start/` (the untouched scratch files `temp.lean`, `temp2.lean`, `Check.lean`, `check_subst.lean` are not part of the library target).
- `#print axioms` on the headline results gives only `propext, Classical.choice, Quot.sound`.
- `python3 scripts/goal_state.py validate` → "OK: 8 tasks validated"; both tasks are now `DONE_STRONG` and every task in the active milestone is complete.

`docs/current-goal-state.md` was re-rendered and `README.md` updated (status, next steps, and the two small helper scripts `scripts/lint_report.py` / `scripts/check_file.sh` that summarise linter warnings for a build log or a single module). `ARISTOTLE_SUMMARY.md` does not exist in this project, so nothing there was touched.
