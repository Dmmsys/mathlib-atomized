/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Typeclasses for measurability of lattice operations

In this file we define classes `MeasurableSup` and `MeasurableInf` and prove dot-style
lemmas (`Measurable.sup`, `AEMeasurable.sup` etc). For binary operations we define two typeclasses:

- `MeasurableSup` says that both left and right sup are measurable;
- `MeasurableSup₂` says that `fun p : α × α => p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableSup₂`
etc. require `α` to have a second countable topology.

For instances relating, e.g., `ContinuousSup` to `MeasurableSup` see file
`MeasureTheory.BorelSpace`.

## Tags

measurable function, lattice operation

-/

public section


open MeasureTheory

/--
Definition of `MeasurableSup` / `MeasurableSup` 的定义

English:
class MeasurableSup
  parameters: (M : Type*) [MeasurableSpace M] [Max M]
  axioms and operations (2):
    - measurable_const_sup : forall c : M, Measurable (c ⊔ ·)  [default: by intro c; fun_prop]
    - measurable_sup_const : forall c : M, Measurable (· ⊔ c)  [default: by intro c; fun_prop]

中文:
类 MeasurableSup
  参数: (M : 类型) [MeasurableSpace M] [Max M]
  公理与运算 (2 个):
    - measurable_const_sup : 对任意 c : M, Measurable (c ⊔ ·)  [默认: by intro c; fun_prop]
    - measurable_sup_const : 对任意 c : M, Measurable (· ⊔ c)  [默认: by intro c; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_sup_const
-/
class MeasurableSup (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_const_sup : forall c : M, Measurable (c ⊔ ·) := by intro c; fun_prop
  measurable_sup_const : forall c : M, Measurable (· ⊔ c) := by intro c; fun_prop

/--
Definition of `MeasurableSup₂` / `MeasurableSup₂` 的定义

English:
class MeasurableSup₂
  parameters: (M : Type*) [MeasurableSpace M] [Max M]
  axioms and operations (1):
    - measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2  [default: by intro p; fun_prop]

中文:
类 MeasurableSup₂
  参数: (M : 类型) [MeasurableSpace M] [Max M]
  公理与运算 (1 个):
    - measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2  [默认: by intro p; fun_prop]

Depends on / 依赖: fun_prop
-/
class MeasurableSup₂ (M : Type*) [MeasurableSpace M] [Max M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2 := by intro p; fun_prop

export MeasurableSup₂ (measurable_sup)

export MeasurableSup (measurable_const_sup measurable_sup_const)

/--
Definition of `MeasurableInf` / `MeasurableInf` 的定义

English:
class MeasurableInf
  parameters: (M : Type*) [MeasurableSpace M] [Min M]
  axioms and operations (2):
    - measurable_const_inf : forall c : M, Measurable (c ⊓ ·)  [default: by intro c; fun_prop]
    - measurable_inf_const : forall c : M, Measurable (· ⊓ c)  [default: by intro c; fun_prop]

中文:
类 MeasurableInf
  参数: (M : 类型) [MeasurableSpace M] [Min M]
  公理与运算 (2 个):
    - measurable_const_inf : 对任意 c : M, Measurable (c ⊓ ·)  [默认: by intro c; fun_prop]
    - measurable_inf_const : 对任意 c : M, Measurable (· ⊓ c)  [默认: by intro c; fun_prop]

Depends on / 依赖: Measurable, fun_prop, measurable_inf_const
-/
class MeasurableInf (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_const_inf : forall c : M, Measurable (c ⊓ ·) := by intro c; fun_prop
  measurable_inf_const : forall c : M, Measurable (· ⊓ c) := by intro c; fun_prop

/--
Definition of `MeasurableInf₂` / `MeasurableInf₂` 的定义

English:
class MeasurableInf₂
  parameters: (M : Type*) [MeasurableSpace M] [Min M]
  axioms and operations (1):
    - measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2  [default: by intro p; fun_prop]

中文:
类 MeasurableInf₂
  参数: (M : 类型) [MeasurableSpace M] [Min M]
  公理与运算 (1 个):
    - measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2  [默认: by intro p; fun_prop]

Depends on / 依赖: fun_prop
-/
class MeasurableInf₂ (M : Type*) [MeasurableSpace M] [Min M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2 := by intro p; fun_prop

export MeasurableInf₂ (measurable_inf)

export MeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type*} [MeasurableSpace M]

section OrderDual

instance (priority := 100) OrderDual.instMeasurableSup [Min M] [MeasurableInf M] :
    MeasurableSup Mᵒᵈ :=
  ⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩

instance (priority := 100) OrderDual.instMeasurableInf [Max M] [MeasurableSup M] :
    MeasurableInf Mᵒᵈ :=
  ⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩

instance (priority := 100) OrderDual.instMeasurableSup₂ [Min M] [MeasurableInf₂ M] :
    MeasurableSup₂ Mᵒᵈ :=
  ⟨@measurable_inf M _ _ _⟩

instance (priority := 100) OrderDual.instMeasurableInf₂ [Max M] [MeasurableSup₂ M] :
    MeasurableInf₂ Mᵒᵈ :=
  ⟨@measurable_sup M _ _ _⟩

end OrderDual

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α -> M}

section Sup

variable [Max M]

section MeasurableSup

variable [MeasurableSup M]

@[fun_prop]
/--
theorem `Measurable.const_sup` / 定理 `Measurable.const_sup`

English:
theorem Measurable.const_sup
  given: (hf : Measurable f) (c : M)
  statement: Measurable fun x => c ⊔ f x
  proof: (measurable_const_sup c).comp hf

@[fun_prop]

中文:
定理 Measurable.const_sup
  条件: (hf : Measurable f) (c : M)
  结论: Measurable fun x => c ⊔ f x
  证明: (measurable_const_sup c).comp hf

@[fun_prop]

Depends on / 依赖: measurable_const_sup
-/
theorem Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔ f x :=
  (measurable_const_sup c).comp hf

@[fun_prop]
/--
theorem `AEMeasurable.const_sup` / 定理 `AEMeasurable.const_sup`

English:
theorem AEMeasurable.const_sup
  given: (hf : AEMeasurable f μ) (c : M)
  proof: (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf

@[fun_prop]

中文:
定理 AEMeasurable.const_sup
  条件: (hf : AEMeasurable f μ) (c : M)
  证明: (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf

@[fun_prop]

Depends on / 依赖: MeasurableSup, MeasurableSup.measurable_const_sup, comp_aemeasurable, measurable_const_sup
-/
theorem AEMeasurable.const_sup (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊔ f x) μ :=
  (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf

@[fun_prop]
/--
theorem `Measurable.sup_const` / 定理 `Measurable.sup_const`

English:
theorem Measurable.sup_const
  given: (hf : Measurable f) (c : M)
  statement: Measurable fun x => f x ⊔ c
  proof: (measurable_sup_const c).comp hf

@[fun_prop]

中文:
定理 Measurable.sup_const
  条件: (hf : Measurable f) (c : M)
  结论: Measurable fun x => f x ⊔ c
  证明: (measurable_sup_const c).comp hf

@[fun_prop]

Depends on / 依赖: measurable_sup_const
-/
theorem Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊔ c :=
  (measurable_sup_const c).comp hf

@[fun_prop]
/--
theorem `AEMeasurable.sup_const` / 定理 `AEMeasurable.sup_const`

English:
theorem AEMeasurable.sup_const
  given: (hf : AEMeasurable f μ) (c : M)
  proof: (measurable_sup_const c).comp_aemeasurable hf

中文:
定理 AEMeasurable.sup_const
  条件: (hf : AEMeasurable f μ) (c : M)
  证明: (measurable_sup_const c).comp_aemeasurable hf

Depends on / 依赖: comp_aemeasurable, measurable_sup_const
-/
theorem AEMeasurable.sup_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊔ c) μ :=
  (measurable_sup_const c).comp_aemeasurable hf

end MeasurableSup

section MeasurableSup₂

variable [MeasurableSup₂ M]

@[to_fun (attr := fun_prop)]
/--
theorem `Measurable.sup` / 定理 `Measurable.sup`

English:
theorem Measurable.sup
  given: (hf : Measurable f) (hg : Measurable g)
  statement: Measurable (f ⊔ g)
  proof: measurable_sup.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.sup' := Measurable.sup

@[to_fun (attr := fun_prop)]

中文:
定理 Measurable.sup
  条件: (hf : Measurable f) (hg : Measurable g)
  结论: Measurable (f ⊔ g)
  证明: measurable_sup.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.sup' := Measurable.sup

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hf.prodMk, measurable_sup, measurable_sup.comp, prodMk
-/
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g) :=
  measurable_sup.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.sup' := Measurable.sup

@[to_fun (attr := fun_prop)]
/--
theorem `AEMeasurable.sup` / 定理 `AEMeasurable.sup`

English:
theorem AEMeasurable.sup
  given: (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: measurable_sup.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.sup' := AEMeasurable.sup

中文:
定理 AEMeasurable.sup
  条件: (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  证明: measurable_sup.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.sup' := AEMeasurable.sup

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_sup, measurable_sup.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.sup (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊔ g) μ :=
  measurable_sup.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.sup' := AEMeasurable.sup

instance (priority := 100) MeasurableSup₂.toMeasurableSup : MeasurableSup M where

end MeasurableSup₂

end Sup

section Inf

variable [Min M]

section MeasurableInf

variable [MeasurableInf M]

@[fun_prop]
/--
theorem `Measurable.const_inf` / 定理 `Measurable.const_inf`

English:
theorem Measurable.const_inf
  given: (hf : Measurable f) (c : M)
  statement: Measurable fun x => c ⊓ f x
  proof: (measurable_const_inf c).comp hf

@[fun_prop]

中文:
定理 Measurable.const_inf
  条件: (hf : Measurable f) (c : M)
  结论: Measurable fun x => c ⊓ f x
  证明: (measurable_const_inf c).comp hf

@[fun_prop]

Depends on / 依赖: measurable_const_inf
-/
theorem Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓ f x :=
  (measurable_const_inf c).comp hf

@[fun_prop]
/--
theorem `AEMeasurable.const_inf` / 定理 `AEMeasurable.const_inf`

English:
theorem AEMeasurable.const_inf
  given: (hf : AEMeasurable f μ) (c : M)
  proof: (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf

@[fun_prop]

中文:
定理 AEMeasurable.const_inf
  条件: (hf : AEMeasurable f μ) (c : M)
  证明: (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf

@[fun_prop]

Depends on / 依赖: MeasurableInf, MeasurableInf.measurable_const_inf, comp_aemeasurable, measurable_const_inf
-/
theorem AEMeasurable.const_inf (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊓ f x) μ :=
  (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf

@[fun_prop]
/--
theorem `Measurable.inf_const` / 定理 `Measurable.inf_const`

English:
theorem Measurable.inf_const
  given: (hf : Measurable f) (c : M)
  statement: Measurable fun x => f x ⊓ c
  proof: (measurable_inf_const c).comp hf

@[fun_prop]

中文:
定理 Measurable.inf_const
  条件: (hf : Measurable f) (c : M)
  结论: Measurable fun x => f x ⊓ c
  证明: (measurable_inf_const c).comp hf

@[fun_prop]

Depends on / 依赖: measurable_inf_const
-/
theorem Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊓ c :=
  (measurable_inf_const c).comp hf

@[fun_prop]
/--
theorem `AEMeasurable.inf_const` / 定理 `AEMeasurable.inf_const`

English:
theorem AEMeasurable.inf_const
  given: (hf : AEMeasurable f μ) (c : M)
  proof: (measurable_inf_const c).comp_aemeasurable hf

中文:
定理 AEMeasurable.inf_const
  条件: (hf : AEMeasurable f μ) (c : M)
  证明: (measurable_inf_const c).comp_aemeasurable hf

Depends on / 依赖: comp_aemeasurable, measurable_inf_const
-/
theorem AEMeasurable.inf_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊓ c) μ :=
  (measurable_inf_const c).comp_aemeasurable hf

end MeasurableInf

section MeasurableInf₂

variable [MeasurableInf₂ M]

@[to_fun (attr := fun_prop)]
/--
theorem `Measurable.inf` / 定理 `Measurable.inf`

English:
theorem Measurable.inf
  given: (hf : Measurable f) (hg : Measurable g)
  statement: Measurable (f ⊓ g)
  proof: measurable_inf.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.inf' := Measurable.inf

@[to_fun (attr := fun_prop)]

中文:
定理 Measurable.inf
  条件: (hf : Measurable f) (hg : Measurable g)
  结论: Measurable (f ⊓ g)
  证明: measurable_inf.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.inf' := Measurable.inf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hf.prodMk, measurable_inf, measurable_inf.comp, prodMk
-/
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g) :=
  measurable_inf.comp (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias Measurable.inf' := Measurable.inf

@[to_fun (attr := fun_prop)]
/--
theorem `AEMeasurable.inf` / 定理 `AEMeasurable.inf`

English:
theorem AEMeasurable.inf
  given: (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: measurable_inf.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.inf' := AEMeasurable.inf

中文:
定理 AEMeasurable.inf
  条件: (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  证明: measurable_inf.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.inf' := AEMeasurable.inf

Depends on / 依赖: comp_aemeasurable, hf.prodMk, measurable_inf, measurable_inf.comp_aemeasurable, prodMk
-/
theorem AEMeasurable.inf (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊓ g) μ :=
  measurable_inf.comp_aemeasurable (hf.prodMk hg)

@[deprecated (since := "2026-06-26")] alias AEMeasurable.inf' := AEMeasurable.inf

instance (priority := 100) MeasurableInf₂.to_hasMeasurableInf : MeasurableInf M where

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type*} [MeasurableSpace δ] [SemilatticeSup α] [MeasurableSup₂ α]

@[fun_prop]
/--
theorem `Finset.measurable_sup'` / 定理 `Finset.measurable_sup'`

English:
theorem Finset.measurable_sup'
  statement: {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι -> δ -> α}
  proof: Finset.sup'_induction hs _ (fun _f hf _g hg => hf.sup hg) fun n hn => hf n hn

@[fun_prop]

中文:
定理 Finset.measurable_sup'
  结论: {ι : 类型} {s : Finset ι} (hs : s.Nonempty) {f : ι -> δ -> α}
  证明: Finset.sup'_induction hs _ (fun _f hf _g hg => hf.sup hg) fun n hn => hf n hn

@[fun_prop]

Depends on / 依赖: Finset, Finset.sup, _induction, hf.sup
-/
theorem Finset.measurable_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι -> δ -> α}
    (hf : forall n in s, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun _f hf _g hg => hf.sup hg) fun n hn => hf n hn

@[fun_prop]
/--
theorem `Finset.measurable_range_sup'` / 定理 `Finset.measurable_range_sup'`

English:
theorem Finset.measurable_range_sup'
  given: {f : Nat -> δ -> α} {n : Nat} (hf : forall k <= n, Measurable (f k))
  proof: by
  refine Finset.measurable_sup' _ ?_
  simpa [Finset.mem_range]

@[fun_prop]

中文:
定理 Finset.measurable_range_sup'
  条件: {f : 自然数 -> δ -> α} {n : 自然数} (hf : 对任意 k <= n, Measurable (f k))
  证明: by
  refine Finset.measurable_sup' _ ?_
  simpa [Finset.mem_range]

@[fun_prop]

Depends on / 依赖: Finset, Finset.measurable_sup, Finset.mem_range, measurable_sup, mem_range
-/
theorem Finset.measurable_range_sup' {f : Nat -> δ -> α} {n : Nat} (hf : forall k <= n, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_add_one f) := by
  refine Finset.measurable_sup' _ ?_
  simpa [Finset.mem_range]

@[fun_prop]
/--
theorem `Finset.measurable_range_sup''` / 定理 `Finset.measurable_range_sup''`

English:
theorem Finset.measurable_range_sup''
  given: {f : Nat -> δ -> α} {n : Nat} (hf : forall k <= n, Measurable (f k))
  proof: by
  convert! Finset.measurable_range_sup' hf using 1
  ext x
  simp

中文:
定理 Finset.measurable_range_sup''
  条件: {f : 自然数 -> δ -> α} {n : 自然数} (hf : 对任意 k <= n, Measurable (f k))
  证明: by
  convert! Finset.measurable_range_sup' hf using 1
  ext x
  simp

Depends on / 依赖: Finset, Finset.measurable_range_sup, convert, measurable_range_sup
-/
theorem Finset.measurable_range_sup'' {f : Nat -> δ -> α} {n : Nat} (hf : forall k <= n, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_add_one fun k => f k x := by
  convert! Finset.measurable_range_sup' hf using 1
  ext x
  simp

end SemilatticeSup
