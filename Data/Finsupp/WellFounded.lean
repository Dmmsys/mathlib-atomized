/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Data.Finsupp.Lex

/-!
# Well-foundedness of the lexicographic and product orders on `Finsupp`

`Finsupp.Lex.wellFounded` and the two variants that follow it essentially say that if `(· > ·)` is
a well order on `α`, `(· < ·)` is well-founded on `N`, and `0` is a bottom element in `N`, then the
lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.Lex.wellFoundedLT_of_finite` says that if `α` is finite and equipped with a linear order
and `(· < ·)` is well-founded on `N`, then the lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.wellFoundedLT` and `wellFoundedLT_of_finite` state the same results for the product
order `(· < ·)`, but without the ordering conditions on `α`.

All results are transferred from `DFinsupp` via `Finsupp.toDFinsupp`.
-/

public section


variable {α N : Type*}

namespace Finsupp

variable [Zero N] {r : α -> α -> Prop} {s : N -> N -> Prop}

/--
theorem `Lex.acc` / 定理 `Lex.acc`

English:
theorem Lex.acc
  statement: (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s) (x : α ->₀ N)
  proof: by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
    simpa only [toDFinsupp_support] using h

中文:
定理 Lex.acc
  结论: (hbot : 对任意 ⦃n⦄, ¬s n 0) (hs : WellFounded s) (x : α ->₀ N)
  证明: by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
    simpa only [toDFinsupp_support] using h
-/
theorem Lex.acc (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s) (x : α ->₀ N)
    (h : forall a in x.support, Acc (rᶜ ⊓ (· != ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
    simpa only [toDFinsupp_support] using h

/--
theorem `Lex.wellFounded` / 定理 `Lex.wellFounded`

English:
theorem Lex.wellFounded
  statement: (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s)
  proof: ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩

中文:
定理 Lex.wellFounded
  结论: (hbot : 对任意 ⦃n⦄, ¬s n 0) (hs : WellFounded s)
  证明: ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
-/
theorem Lex.wellFounded (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    (hr : WellFounded <| rᶜ ⊓ (· != ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩

/--
theorem `Lex.wellFounded'` / 定理 `Lex.wellFounded'`

English:
theorem Lex.wellFounded'
  statement: (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s)
  proof: (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)

中文:
定理 Lex.wellFounded'
  结论: (hbot : 对任意 ⦃n⦄, ¬s n 0) (hs : WellFounded s)
  证明: (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)
-/
theorem Lex.wellFounded' (hbot : forall ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (Finsupp.Lex r s) :=
  (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)

/--
Instance `Lex.wellFoundedLT` / 实例 `Lex.wellFoundedLT`

English:
instance Lex.wellFoundedLT
  signature: {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα : WellFoundedGT α]
  body: ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩

中文:
实例 Lex.wellFoundedLT
  签名: {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα : WellFoundedGT α]
  定义体: ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩
-/
instance Lex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα : WellFoundedGT α]
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
    [hN : WellFoundedLT N] : WellFoundedLT (Lex (α ->₀ N)) :=
  ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩

/--
Instance `Colex.wellFoundedLT` / 实例 `Colex.wellFoundedLT`

English:
instance Colex.wellFoundedLT
  signature: {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
  body: Lex.wellFoundedLT (α := αᵒᵈ)

中文:
实例 Colex.wellFoundedLT
  签名: {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
  定义体: Lex.wellFoundedLT (α := αᵒᵈ)
-/
instance Colex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α ->₀ N)) :=
  Lex.wellFoundedLT (α := αᵒᵈ)

variable (r)

/--
theorem `Lex.wellFounded_of_finite` / 定理 `Lex.wellFounded_of_finite`

English:
theorem Lex.wellFounded_of_finite
  statement: [IsStrictTotalOrder α r] [Finite α]
  proof: InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)

中文:
定理 Lex.wellFounded_of_finite
  结论: [IsStrictTotalOrder α r] [Finite α]
  证明: InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)

Depends on / 依赖: InvImage, InvImage.wf, Pi.Lex.wellFounded, equivFunOnFinite, wellFounded
-/
theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)

/--
theorem `Lex.wellFoundedLT_of_finite` / 定理 `Lex.wellFoundedLT_of_finite`

English:
theorem Lex.wellFoundedLT_of_finite
  statement: [LinearOrder α] [Finite α] [LT N]
  proof: ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩

中文:
定理 Lex.wellFoundedLT_of_finite
  结论: [LinearOrder α] [Finite α] [LT N]
  证明: ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩

Depends on / 依赖: Finsupp, Finsupp.Lex.wellFounded_of_finite, wellFounded_of_finite
-/
theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [hwf : WellFoundedLT N] : WellFoundedLT (Lex (α ->₀ N)) :=
  ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩

/--
theorem `Colex.wellFoundedLT_of_finite` / 定理 `Colex.wellFoundedLT_of_finite`

English:
theorem Colex.wellFoundedLT_of_finite
  statement: [LinearOrder α] [Finite α] [LT N]
  proof: Lex.wellFoundedLT_of_finite (α := αᵒᵈ)

中文:
定理 Colex.wellFoundedLT_of_finite
  结论: [LinearOrder α] [Finite α] [LT N]
  证明: Lex.wellFoundedLT_of_finite (α := αᵒᵈ)

Depends on / 依赖: Lex.wellFoundedLT_of_finite, wellFoundedLT_of_finite
-/
theorem Colex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α ->₀ N)) :=
  Lex.wellFoundedLT_of_finite (α := αᵒᵈ)

/--
theorem `wellFoundedLT` / 定理 `wellFoundedLT`

English:
theorem wellFoundedLT
  given: [Preorder N] [WellFoundedLT N] (hbot : forall n : N, ¬n < 0)
  proof: ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩

中文:
定理 wellFoundedLT
  条件: [Preorder N] [WellFoundedLT N] (hbot : 对任意 n : N, ¬n < 0)
  证明: ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩
-/
protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot : forall n : N, ¬n < 0) :
    WellFoundedLT (α ->₀ N) :=
  ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩

/--
Instance `wellFoundedLT'` / 实例 `wellFoundedLT'`

English:
instance wellFoundedLT'
  signature: {N}
  body: Finsupp.wellFoundedLT fun _ => not_lt_zero

中文:
实例 wellFoundedLT'
  签名: {N}
  定义体: Finsupp.wellFoundedLT fun _ => not_lt_zero

Depends on / 依赖: Finsupp, Finsupp.wellFoundedLT, not_lt_zero, wellFoundedLT
-/
instance wellFoundedLT' {N}
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N] [WellFoundedLT N] :
    WellFoundedLT (α ->₀ N) :=
  Finsupp.wellFoundedLT fun _ => not_lt_zero

/--
Instance `wellFoundedLT_of_finite` / 实例 `wellFoundedLT_of_finite`

English:
instance wellFoundedLT_of_finite
  signature: [Finite α] [Preorder N] [WellFoundedLT N]
  body: ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩

中文:
实例 wellFoundedLT_of_finite
  签名: [Finite α] [Preorder N] [WellFoundedLT N]
  定义体: ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩

Depends on / 依赖: Function, Function.wellFoundedLT.wf, InvImage, InvImage.wf, equivFunOnFinite, wellFoundedLT
-/
instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N] :
    WellFoundedLT (α ->₀ N) :=
  ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩

end Finsupp
