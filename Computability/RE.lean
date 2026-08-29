/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Computable and Recursively Enumerable Predicates

This file defines computable (`ComputablePred`) and recursively enumerable (`REPred`)
predicates. It also provides basic closure properties and Post's theorem on the
equivalence of recursive, r.e., and co-r.e. sets.
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

/--
theorem `merge'` / 定理 `merge'`

English:
theorem merge'
  given: {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g)
  proof: by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n > cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.primrec_evaln.to_com

中文:
定理 merge'
  条件: {f g} (hf : 自然数.Partrec f) (hg : 自然数.Partrec g)
  证明: by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n > cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.primrec_evaln.to_com

Depends on / 依赖: Code.eval, Code.evaln, Code.exists_code, Code.primrec_evaln.to_comp.comp, Nat.Partrec, Nat.rfindOpt, Partrec, Partrec.nat_iff, Partrec.rfindOpt, Primrec, Primrec.option_orElse.to_comp.comp, cf.evaln, cg.evaln, exists_code, nat_iff, option_orElse, primrec_evaln, rfindOpt, snd.pair, to_comp
-/
theorem merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) :
    exists h, Nat.Partrec h ∧
      forall a, (forall x in h a, x in f a ∨ x in g a) ∧ ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  obtain ⟨cf, rfl⟩ := Code.exists_code.1 hf
  obtain ⟨cg, rfl⟩ := Code.exists_code.1 hg
have : Nat.Partrec fun n => Nat.rfindOpt fun k => cf.evaln k n > cg.evaln k n :=
    Partrec.nat_iff.1
      (Partrec.rfindOpt <|
        Primrec.option_orElse.to_comp.comp
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cf)).pair fst)
          (Code.primrec_evaln.to_comp.comp <| (snd.pair (const cg)).pair fst))
  refine ⟨_, this, fun n => ?_⟩
have : forall x in rfindOpt fun k => Code.evaln k cf n > Code.evaln k cg n,
      x in Code.eval cf n ∨ x in Code.eval cg n := by
    intro x h
    obtain ⟨k, e⟩ := Nat.rfindOpt_spec h
    rw [Option.mem_def]; rw [Option.orElse_eq_some]; rw [← Option.mem_def]; rw [← Option.mem_def] at e
    obtain e | ⟨-, e⟩ := e <;> simp [Code.evaln_sound e]
  refine ⟨this, fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, fun h => ?_⟩
  rw [Nat.rfindOpt_dom]
  simp only [dom_iff_mem, Code.evaln_complete, Option.mem_def] at h
  obtain ⟨x, k, e⟩ | ⟨x, k, e⟩ := h
  · exact ⟨k, x, by simp [e]⟩
  · refine ⟨k, ?_⟩
    rcases cf.evaln k n with - | y
    · exact ⟨x, by simp [e]⟩
    · exact ⟨y, by simp⟩

end Nat.Partrec

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open Nat.Partrec (Code)

open Nat.Partrec.Code

/--
theorem `merge'` / 定理 `merge'`

English:
theorem merge'
  given: {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
  proof: by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have 

中文:
定理 merge'
  条件: {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
  证明: by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have 

Depends on / 依赖: Computable, Computable.decode.ofOption.comp, Computable.encode, Nat.Partrec.merge, Option.mem_def, Partrec, bind_some, coe_some, decode, encode, mem_bind_iff, mem_coe, mem_def, mem_map, nat_iff, ofOption
-/
theorem merge' {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g) :
    exists k : α ->. σ,
      Partrec k ∧ forall a, (forall x in k a, x in f a ∨ x in g a) ∧ ((k a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by
  let ⟨k, hk, H⟩ := Nat.Partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg)
  let k' (a : α) := (k (encode a)).bind fun n => (decode (α := σ) n : Part σ)
  refine
    ⟨k', ((nat_iff.2 hk).comp Computable.encode).bind (Computable.decode.ofOption.comp snd).to₂,
      fun a => ?_⟩
  have : forall x in k' a, x in f a ∨ x in g a := by
    intro x h'
    simp only [k', mem_coe, mem_bind_iff, Option.mem_def] at h'
    obtain ⟨n, hn, hx⟩ := h'
    have := (H _).1 _ hn
    simp only [decode₂_encode, coe_some, bind_some, mem_map_iff] at this
    obtain ⟨a', ha, rfl⟩ | ⟨a', ha, rfl⟩ := this <;> simp only [encodek, Option.some_inj] at hx <;>
      rw [hx] at ha
    · exact Or.inl ha
    · exact Or.inr ha
  refine ⟨this, ⟨fun h => (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, ?_⟩⟩
  intro h
  rw [bind_dom]
  have hk : (k (encode a)).Dom :=
    (H _).2.2 (by simpa only [encodek₂, bind_some, coe_some] using! h)
  exists hk
  simp only [mem_map_iff, mem_coe, mem_bind_iff, Option.mem_def] at H
  obtain ⟨a', _, y, _, e⟩ | ⟨a', _, y, _, e⟩ := (H _).1 _ ⟨hk, rfl⟩ <;>
    simp only [e.symm, encodek, coe_some, some_dom]

/--
theorem `merge` / 定理 `merge`

English:
theorem merge
  statement: {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
  proof: let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      rcases h with h | h <;> rcases (K _).1 _ ⟨this, rfl⟩ with h' | h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h')

中文:
定理 merge
  结论: {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
  证明: let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      rcases h with h | h <;> rcases (K _).1 _ ⟨this, rfl⟩ with h' | h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h')

Depends on / 依赖: Exists, Exists.fst, h.imp, mem_unique
-/
theorem merge {f g : α ->. σ} (hf : Partrec f) (hg : Partrec g)
    (H : forall (a), forall x in f a, forall y in g a, x = y) :
    exists k : α ->. σ, Partrec k ∧ forall a x, x in k a ↔ x in f a ∨ x in g a :=
  let ⟨k, hk, K⟩ := merge' hf hg
  ⟨k, hk, fun a x =>
    ⟨(K _).1 _, fun h => by
      have : (k a).Dom := (K _).2.2 (h.imp Exists.fst Exists.fst)
      refine ⟨this, ?_⟩
      rcases h with h | h <;> rcases (K _).1 _ ⟨this, rfl⟩ with h' | h'
      · exact mem_unique h' h
      · exact (H _ _ h _ h').symm
      · exact H _ _ h' _ h
      · exact mem_unique h' h⟩⟩

/--
theorem `cond` / 定理 `cond`

English:
theorem cond
  statement: {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Computable c) (hf : Partrec f)
  proof: let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]

nonrec theorem sumCasesOn {f : α

中文:
定理 cond
  结论: {c : α -> 布尔} {f : α ->. σ} {g : α ->. σ} (hc : Computable c) (hf : Partrec f)
  证明: let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]

nonrec theorem sumCasesOn {f : α

Depends on / 依赖: Computable, Computable.cond, Computable.decode, Computable.encode, decode, encode, encodek, eval_part, eval_part.comp, exists_code, ofOption, ofOption.to, of_eq
-/
theorem cond {c : α -> Bool} {f : α ->. σ} {g : α ->. σ} (hc : Computable c) (hf : Partrec f)
    (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a) :=
  let ⟨cf, ef⟩ := exists_code.1 hf
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.encode).bind
    ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq
    fun a => by cases c a <;> simp [ef, eg, encodek]

nonrec theorem sumCasesOn {f : α -> β oplus γ} {g : α -> β ->. σ} {h : α -> γ ->. σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Partrec₂ h) : @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
option_some_iff.1
    (cond (sumCasesOn hf (const true).to₂ (const false).to₂)
          (sumCasesOn_left hf (option_some_iff.2 hg).to₂ (const Option.none).to₂)
          (sumCasesOn_right hf (const Option.none).to₂ (option_some_iff.2 hh).to₂)).of_eq
      fun a => by cases f a <;> simp only [Bool.cond_true, Bool.cond_false]

end Partrec

/--
Definition of `ComputablePred` / `ComputablePred` 的定义

English:
definition ComputablePred
  signature: {α} [Primcodable α] (p : α -> Prop)
  body: exists (_ : DecidablePred p), Computable fun a => decide (p a)

中文:
定义 ComputablePred
  签名: {α} [Primcodable α] (p : α -> 命题)
  定义体: exists (_ : DecidablePred p), Computable fun a => decide (p a)

Depends on / 依赖: Computable, DecidablePred
-/
def ComputablePred {α} [Primcodable α] (p : α -> Prop) :=
  exists (_ : DecidablePred p), Computable fun a => decide (p a)

section decide

variable {α} [Primcodable α]

/--
lemma `ComputablePred.decide` / 引理 `ComputablePred.decide`

English:
lemma ComputablePred.decide
  given: {p : α -> Prop} [DecidablePred p] (hp : ComputablePred p)
  proof: by
  convert! hp.choose_spec

中文:
引理 ComputablePred.decide
  条件: {p : α -> 命题} [DecidablePred p] (hp : ComputablePred p)
  证明: by
  convert! hp.choose_spec
-/
protected lemma ComputablePred.decide {p : α -> Prop} [DecidablePred p] (hp : ComputablePred p) :
    Computable (fun a => decide (p a)) := by
  convert! hp.choose_spec

/--
lemma `Computable.computablePred` / 引理 `Computable.computablePred`

English:
lemma Computable.computablePred
  statement: {p : α -> Prop} [DecidablePred p]
  proof: ⟨inferInstance, hp⟩

中文:
引理 Computable.computablePred
  结论: {p : α -> 命题} [DecidablePred p]
  证明: ⟨inferInstance, hp⟩
-/
lemma Computable.computablePred {p : α -> Prop} [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) : ComputablePred p :=
  ⟨inferInstance, hp⟩

/--
lemma `computablePred_iff_computable_decide` / 引理 `computablePred_iff_computable_decide`

English:
lemma computablePred_iff_computable_decide
  given: {p : α -> Prop} [DecidablePred p]
  proof: ComputablePred.decide
  mpr := Computable.computablePred

中文:
引理 computablePred_iff_computable_decide
  条件: {p : α -> 命题} [DecidablePred p]
  证明: ComputablePred.decide
  mpr := Computable.computablePred

Depends on / 依赖: ComputablePred, ComputablePred.decide
-/
lemma computablePred_iff_computable_decide {p : α -> Prop} [DecidablePred p] :
    ComputablePred p ↔ Computable (fun a => decide (p a)) where
  mp := ComputablePred.decide
  mpr := Computable.computablePred

/--
lemma `PrimrecPred.computablePred` / 引理 `PrimrecPred.computablePred`

English:
lemma PrimrecPred.computablePred
  given: {α} [Primcodable α] {p : α -> Prop}

中文:
引理 PrimrecPred.computablePred
  条件: {α} [Primcodable α] {p : α -> 命题}
-/
lemma PrimrecPred.computablePred {α} [Primcodable α] {p : α -> Prop} :
    (hp : PrimrecPred p) -> ComputablePred p
  | ⟨_, hp⟩ => hp.to_comp.computablePred

end decide

/--
Definition of `REPred` / `REPred` 的定义

English:
definition REPred
  signature: {α} [Primcodable α] (p : α -> Prop)
  body: Partrec fun a => Part.assert (p a) fun _ => Part.some ()

中文:
定义 REPred
  签名: {α} [Primcodable α] (p : α -> 命题)
  定义体: Partrec fun a => Part.assert (p a) fun _ => Part.some ()

Depends on / 依赖: Part.assert, Part.some, Partrec, assert
-/
def REPred {α} [Primcodable α] (p : α -> Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

/--
theorem `REPred.of_eq` / 定理 `REPred.of_eq`

English:
theorem REPred.of_eq
  given: {α} [Primcodable α] {p q : α -> Prop} (hp : REPred p) (H : forall a, p a ↔ q a)
  proof: (funext fun a => propext (H a) : p = q) ▸ hp

中文:
定理 REPred.of_eq
  条件: {α} [Primcodable α] {p q : α -> 命题} (hp : REPred p) (H : 对任意 a, p a ↔ q a)
  证明: (funext fun a => propext (H a) : p = q) ▸ hp

Depends on / 依赖: propext
-/
theorem REPred.of_eq {α} [Primcodable α] {p q : α -> Prop} (hp : REPred p) (H : forall a, p a ↔ q a) :
    REPred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

/--
theorem `Partrec.dom_re` / 定理 `Partrec.dom_re`

English:
theorem Partrec.dom_re
  given: {α β} [Primcodable α] [Primcodable β] {f : α ->. β} (h : Partrec f)
  proof: (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]

中文:
定理 Partrec.dom_re
  条件: {α β} [Primcodable α] [Primcodable β] {f : α ->. β} (h : Partrec f)
  证明: (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]

Depends on / 依赖: Computable, Computable.const, Part.dom_iff_mem, Part.ext, dom_iff_mem, h.map, of_eq
-/
theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α ->. β} (h : Partrec f) :
    REPred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq fun n => Part.ext fun _ => by simp [Part.dom_iff_mem]

/--
theorem `ComputablePred.of_eq` / 定理 `ComputablePred.of_eq`

English:
theorem ComputablePred.of_eq
  statement: {α} [Primcodable α] {p q : α -> Prop} (hp : ComputablePred p)
  proof: (funext fun a => propext (H a) : p = q) ▸ hp

中文:
定理 ComputablePred.of_eq
  结论: {α} [Primcodable α] {p q : α -> 命题} (hp : ComputablePred p)
  证明: (funext fun a => propext (H a) : p = q) ▸ hp

Depends on / 依赖: propext
-/
theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α -> Prop} (hp : ComputablePred p)
    (H : forall a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace Computable

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `find` / 引理 `find`

English:
lemma find
  statement: {α : Type*} [Primcodable α] {P : α -> Nat -> Prop} [DecidableRel P]
  proof: by
  have h : Partrec (fun x => Nat.rfind fun n => Part.some (decide (P x n))) :=
    Partrec.rfind hP_comp.decide.partrec
  refine h.of_eq_tot fun x => ?_
  simp +contextual [Nat.find_spec]

中文:
引理 find
  结论: {α : 类型} [Primcodable α] {P : α -> 自然数 -> 命题} [DecidableRel P]
  证明: by
  have h : Partrec (fun x => Nat.rfind fun n => Part.some (decide (P x n))) :=
    Partrec.rfind hP_comp.decide.partrec
  refine h.of_eq_tot fun x => ?_
  simp +contextual [Nat.find_spec]

Depends on / 依赖: Nat.find_spec, Nat.rfind, Part.some, Partrec, Partrec.rfind, contextual, find_spec, h.of_eq_tot, hP_comp, hP_comp.decide.partrec, of_eq_tot, partrec
-/
lemma find {α : Type*} [Primcodable α] {P : α -> Nat -> Prop} [DecidableRel P]
    (hP_comp : ComputablePred (fun p : α × Nat => P p.1 p.2)) (hP_ex : forall x, exists n, P x n) :
    Computable (fun x => Nat.find (hP_ex x)) := by
  have h : Partrec (fun x => Nat.rfind fun n => Part.some (decide (P x n))) :=
    Partrec.rfind hP_comp.decide.partrec
  refine h.of_eq_tot fun x => ?_
  simp +contextual [Nat.find_spec]

end Computable

namespace ComputablePred

variable {α : Type*} [Primcodable α]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

/--
theorem `computable_iff` / 定理 `computable_iff`

English:
theorem computable_iff
  given: {p : α -> Prop}
  proof: ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩

中文:
定理 computable_iff
  条件: {p : α -> 命题}
  证明: ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩

Depends on / 依赖: Bool.decide_iff, decide_iff, infer_instance, propext
-/
theorem computable_iff {p : α -> Prop} :
    ComputablePred p ↔ exists f : α -> Bool, Computable f ∧ p = fun a => (f a : Prop) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h, funext fun _ => propext (Bool.decide_iff _).symm⟩, by
    rintro ⟨f, h, rfl⟩; exact ⟨by infer_instance, by simpa using h⟩⟩

/--
theorem `not` / 定理 `not`

English:
theorem not
  given: {p : α -> Prop}

中文:
定理 not
  条件: {p : α -> 命题}
-/
protected theorem not {p : α -> Prop} :
    (hp : ComputablePred p) -> ComputablePred fun a => ¬p a
| ⟨_, hp⟩ => Computable.computablePred .of_eq by simp Primrec.not.to_comp.comp hp

/--
theorem `ite` / 定理 `ite`

English:
theorem ite
  statement: {f₁ f₂ : Nat -> Nat} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
  proof: by
  simpa [Bool.cond_decide] using hc.decide.cond hf₁ hf₂

中文:
定理 ite
  结论: {f₁ f₂ : 自然数 -> 自然数} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
  证明: by
  simpa [Bool.cond_decide] using hc.decide.cond hf₁ hf₂

Depends on / 依赖: Bool.cond_decide, cond_decide, hc.decide.cond
-/
theorem ite {f₁ f₂ : Nat -> Nat} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
    {c : Nat -> Prop} [DecidablePred c] (hc : ComputablePred c) :
    Computable fun k => if c k then f₁ k else f₂ k := by
  simpa [Bool.cond_decide] using hc.decide.cond hf₁ hf₂

/--
theorem `to_re` / 定理 `to_re`

English:
theorem to_re
  given: {p : α -> Prop} (hp : ComputablePred p)
  statement: REPred p
  proof: by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

中文:
定理 to_re
  条件: {p : α -> 命题} (hp : ComputablePred p)
  结论: REPred p
  证明: by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

Depends on / 依赖: Decidable, Decidable.Partrec.const, Part.ext, Part.some, Partrec, Partrec.cond, Partrec.none, REPred, computable_iff, of_eq
-/
theorem to_re {p : α -> Prop} (hp : ComputablePred p) : REPred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

-- Post's theorem on the equivalence of r.e., co-r.e. sets and
-- computable sets. The assumption that p is decidable is required
-- unless we assume Markov's principle or LEM.
set_option linter.unusedDecidableInType false in
/--
theorem `computable_iff_re_compl_re` / 定理 `computable_iff_re_compl_re`

English:
theorem computable_iff_re_compl_re
  given: {p : α -> Prop} [DecidablePred p]
  proof: ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_som

中文:
定理 computable_iff_re_compl_re
  条件: {p : α -> 命题} [DecidablePred p]
  证明: ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_som

Depends on / 依赖: Computable, Computable.const, Part.eq_some_iff, Part.mem_assert_iff, Part.mem_map_iff, Part.mem_some_iff, Partrec, Partrec.merge, Partrec.of_eq, and_true, eq_some_iff, exists_const, exists_prop, h.not.to_re, h.to_re, mem_assert_iff, mem_map_iff, mem_some_iff, of_eq, to_re
-/
theorem computable_iff_re_compl_re {p : α -> Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a :=
  ⟨fun h => ⟨h.to_re, h.not.to_re⟩, fun ⟨h₁, h₂⟩ =>
    ⟨‹_›, by
      obtain ⟨k, pk, hk⟩ :=
        Partrec.merge (h₁.map (Computable.const true).to₂) (h₂.map (Computable.const false).to₂)
        (by
          intro a x hx y hy
          simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop,
            and_true, exists_const] at hx hy
          cases hy.1 hx.1)
      refine Partrec.of_eq pk fun n => Part.eq_some_iff.2 ?_
      rw [hk]
      simp only [Part.mem_map_iff, Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true,
        true_eq_decide_iff, and_self, exists_const, false_eq_decide_iff]
      apply Decidable.em⟩⟩

/--
theorem `computable_iff_re_compl_re'` / 定理 `computable_iff_re_compl_re'`

English:
theorem computable_iff_re_compl_re'
  given: {p : α -> Prop}
  proof: by
  classical exact computable_iff_re_compl_re

中文:
定理 computable_iff_re_compl_re'
  条件: {p : α -> 命题}
  证明: by
  classical exact computable_iff_re_compl_re

Depends on / 依赖: classical, computable_iff_re_compl_re
-/
theorem computable_iff_re_compl_re' {p : α -> Prop} :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by
  classical exact computable_iff_re_compl_re

end ComputablePred
