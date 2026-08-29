/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.RE
public import Mathlib.Data.Set.Subsingleton

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

public section

open Encodable Denumerable
open Computable Part
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace ComputablePred

variable {α : Type*} [Primcodable α]

/--
theorem `rice` / 定理 `rice`

English:
theorem rice
  statement: (C : Set (Nat ->. Nat)) (h : ComputablePred fun c => eval c in C) {f g} (hf : Nat.Partrec f)
  proof: by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c in C <;> simp_all

中文:
定理 rice
  结论: (C : Set (自然数 ->. 自然数)) (h : ComputablePred fun c => eval c in C) {f g} (hf : 自然数.Partrec f)
  证明: by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c in C <;> simp_all

Depends on / 依赖: Bool.cond_decide, Partrec, Partrec.cond, Partrec.nat_iff, cond_decide, h.comp, nat_iff
-/
theorem rice (C : Set (Nat ->. Nat)) (h : ComputablePred fun c => eval c in C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f in C) : g in C := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂
          ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : eval c in C <;> simp_all

/--
theorem `rice₂` / 定理 `rice₂`

English:
theorem rice₂
  given: (C : Set Code) (H : forall cf cg, eval cf = eval cg -> (cf in C ↔ cg in C))
  proof: by
  exact
      have hC : forall f, f in C ↔ eval f in eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C

中文:
定理 rice₂
  条件: (C : Set Code) (H : 对任意 cf cg, eval cf = eval cg -> (cf in C ↔ cg in C))
  证明: by
  exact
      have hC : forall f, f in C ↔ eval f in eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C

Depends on / 依赖: Computable, Computable.id, ComputablePred, Partrec, Partrec.nat_iff, Set.eq_univ_of_forall, Set.mem, Set.mem_image_of_mem, Set.nonempty_iff_ne_empty, eq_univ_of_forall, eval_part, eval_part.comp, h.of_eq, mem_image_of_mem, nat_iff, nonempty_iff_ne_empty, of_eq, or_iff_not_imp_left
-/
theorem rice₂ (C : Set Code) (H : forall cf cg, eval cf = eval cg -> (cf in C ↔ cg in C)) :
    (ComputablePred fun c => c in C) ↔ C = ∅ ∨ C = Set.univ := by
  exact
      have hC : forall f, f in C ↔ eval f in eval '' C := fun f =>
        ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
      ⟨fun h =>
        or_iff_not_imp_left.2 fun C0 =>
          Set.eq_univ_of_forall fun cg =>
            let ⟨cf, fC⟩ := Set.nonempty_iff_ne_empty.2 C0
(hC _).2
              rice (eval '' C) (h.of_eq hC)
                (Partrec.nat_iff.1 <| eval_part.comp (const cf) Computable.id)
                (Partrec.nat_iff.1 <| eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
        fun h => by {
          obtain rfl | rfl := h <;> simpa [ComputablePred, Set.mem_empty_iff_false] using
            Computable.const _}⟩

/--
theorem `halting_problem_re` / 定理 `halting_problem_re`

English:
theorem halting_problem_re
  given: (n)
  statement: REPred fun c => (eval c n).Dom
  proof: (eval_part.comp Computable.id (Computable.const _)).dom_re

中文:
定理 halting_problem_re
  条件: (n)
  结论: REPred fun c => (eval c n).Dom
  证明: (eval_part.comp Computable.id (Computable.const _)).dom_re

Depends on / 依赖: Computable, Computable.const, Computable.id, dom_re, eval_part, eval_part.comp
-/
theorem halting_problem_re (n) : REPred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re

/--
theorem `halting_problem` / 定理 `halting_problem`

English:
theorem halting_problem
  given: (n)
  statement: ¬ComputablePred fun c => (eval c n).Dom

中文:
定理 halting_problem
  条件: (n)
  结论: ¬ComputablePred fun c => (eval c n).Dom
-/
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
  | h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivial

/--
theorem `halting_problem_not_re` / 定理 `halting_problem_not_re`

English:
theorem halting_problem_not_re
  given: (n)
  statement: ¬REPred fun c => ¬(eval c n).Dom

中文:
定理 halting_problem_not_re
  条件: (n)
  结论: ¬REPred fun c => ¬(eval c n).Dom
-/
theorem halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom
| h => halting_problem _ computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred
