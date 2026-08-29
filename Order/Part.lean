/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Part
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.Common

/-!
# Monotonicity of monadic operations on `Part`
-/

@[expose] public section

open Part

variable {α β γ : Type*} [Preorder α]

section bind
variable {f : α -> Part β} {g : α -> β -> Part γ}

/--
lemma `Monotone.partBind` / 引理 `Monotone.partBind`

English:
lemma Monotone.partBind
  given: (hf : Monotone f) (hg : Monotone g)
  proof: by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

中文:
引理 递增.partBind
  条件: (hf : 递增 f) (hg : 递增 g)
  证明: by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

Depends on / 依赖: Part.mem_bind_iff, and_imp, exists_imp, mem_bind_iff
-/
lemma Monotone.partBind (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

/--
lemma `Antitone.partBind` / 引理 `Antitone.partBind`

English:
lemma Antitone.partBind
  given: (hf : Antitone f) (hg : Antitone g)
  proof: by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

中文:
引理 递减.partBind
  条件: (hf : 递减 f) (hg : 递减 g)
  证明: by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

Depends on / 依赖: Part.mem_bind_iff, and_imp, exists_imp, mem_bind_iff
-/
lemma Antitone.partBind (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => (f x).bind (g x) := by
  rintro x y h a
  simp only [and_imp, Part.mem_bind_iff, exists_imp]
  exact fun b hb ha => ⟨b, hf h _ hb, hg h _ _ ha⟩

end bind

section map
variable {f : β -> γ} {g : α -> Part β}

/--
lemma `Monotone.partMap` / 引理 `Monotone.partMap`

English:
lemma Monotone.partMap
  given: (hg : Monotone g)
  statement: Monotone fun x => (g x).map f
  proof: by
  simpa only [← bind_some_eq_map] using hg.partBind monotone_const

中文:
引理 递增.partMap
  条件: (hg : 递增 g)
  结论: 递增 fun x => (g x).map f
  证明: by
  simpa only [← bind_some_eq_map] using hg.partBind monotone_const

Depends on / 依赖: bind_some_eq_map, hg.partBind, monotone_const, partBind
-/
lemma Monotone.partMap (hg : Monotone g) : Monotone fun x => (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind monotone_const

/--
lemma `Antitone.partMap` / 引理 `Antitone.partMap`

English:
lemma Antitone.partMap
  given: (hg : Antitone g)
  statement: Antitone fun x => (g x).map f
  proof: by
  simpa only [← bind_some_eq_map] using hg.partBind antitone_const

中文:
引理 递减.partMap
  条件: (hg : 递减 g)
  结论: 递减 fun x => (g x).map f
  证明: by
  simpa only [← bind_some_eq_map] using hg.partBind antitone_const

Depends on / 依赖: antitone_const, bind_some_eq_map, hg.partBind, partBind
-/
lemma Antitone.partMap (hg : Antitone g) : Antitone fun x => (g x).map f := by
  simpa only [← bind_some_eq_map] using hg.partBind antitone_const

end map

section seq
variable {β γ : Type _} {f : α -> Part (β -> γ)} {g : α -> Part β}

/--
lemma `Monotone.partSeq` / 引理 `Monotone.partSeq`

English:
lemma Monotone.partSeq
  given: (hf : Monotone f) (hg : Monotone g)
  statement: Monotone fun x => f x <*> g x
  proof: by
simpa only [seq_eq_bind_map] using! hf.partBind Monotone.of_apply₂ fun _ => hg.partMap

中文:
引理 递增.partSeq
  条件: (hf : 递增 f) (hg : 递增 g)
  结论: 递增 fun x => f x <*> g x
  证明: by
simpa only [seq_eq_bind_map] using! hf.partBind Monotone.of_apply₂ fun _ => hg.partMap

Depends on / 依赖: Monotone, Monotone.of_apply, hf.partBind, hg.partMap, partBind, partMap, seq_eq_bind_map
-/
lemma Monotone.partSeq (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x <*> g x := by
simpa only [seq_eq_bind_map] using! hf.partBind Monotone.of_apply₂ fun _ => hg.partMap

/--
lemma `Antitone.partSeq` / 引理 `Antitone.partSeq`

English:
lemma Antitone.partSeq
  given: (hf : Antitone f) (hg : Antitone g)
  statement: Antitone fun x => f x <*> g x
  proof: by
simpa only [seq_eq_bind_map] using! hf.partBind Antitone.of_apply₂ fun _ => hg.partMap

中文:
引理 递减.partSeq
  条件: (hf : 递减 f) (hg : 递减 g)
  结论: 递减 fun x => f x <*> g x
  证明: by
simpa only [seq_eq_bind_map] using! hf.partBind Antitone.of_apply₂ fun _ => hg.partMap

Depends on / 依赖: Antitone, Antitone.of_apply, hf.partBind, hg.partMap, partBind, partMap, seq_eq_bind_map
-/
lemma Antitone.partSeq (hf : Antitone f) (hg : Antitone g) : Antitone fun x => f x <*> g x := by
simpa only [seq_eq_bind_map] using! hf.partBind Antitone.of_apply₂ fun _ => hg.partMap

end seq

namespace OrderHom

/-- `Part.bind` as a monotone function -/
@[simps]
/--
Definition of `partBind` / `partBind` 的定义

English:
definition partBind
  signature: (f : α ->o Part β) (g : α ->o β -> Part γ)
  body: (f x).bind (g x)
  monotone' := f.2.partBind g.2

中文:
定义 partBind
  签名: (f : α ->o Part β) (g : α ->o β -> Part γ)
  定义体: (f x).bind (g x)
  monotone' := f.2.partBind g.2
-/
def partBind (f : α ->o Part β) (g : α ->o β -> Part γ) : α ->o Part γ where
  toFun x := (f x).bind (g x)
  monotone' := f.2.partBind g.2

end OrderHom
