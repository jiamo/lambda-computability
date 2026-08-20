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
