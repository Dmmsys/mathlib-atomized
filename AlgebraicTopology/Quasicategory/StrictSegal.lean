/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Strict Segal simplicial sets are quasicategories

In `AlgebraicTopology.SimplicialSet.StrictSegal`, we define the strict Segal
condition on a simplicial set `X`. We say that `X` is strict Segal if its
simplices are uniquely determined by their spine.

In this file, we prove that any simplicial set satisfying the strict Segal
condition is a quasicategory.
-/

public section

universe u

open CategoryTheory
open Simplicial SimplicialObject SimplexCategory

namespace SSet.StrictSegal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Any `StrictSegal` simplicial set is a `Quasicategory`. -/
/-
**SSet.StrictSegal.quasicategory** 是 Mathlib 中的一个定理，位于命名空间 `SSet.StrictSegal`。
形式化陈述：quasicategory {X : SSet.{u}} (sx : StrictSegal X) : Quasicategory X
参数：sx : StrictSegal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.quasicategory_of_filler`：quasicategory_of_filler (S : SSet) (filler
 : forall ⦃n : Nat⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S) (_h0 : 0 <
 i) (_hn : i < Fin…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SSet.StrictSegal.spineInjective`：spineInjective : Function.Injective (sx
.spineEquiv n)
· 使用引理 `SSet.Path.ext'`：ext' {f g : Path X (n + 1)} (h : forall i, f.arrow i = g
.arrow i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_comp_apply`：types_comp_apply {X Y Z : Type u} (f : 
X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `SSet.spine_arrow`：spine_arrow (Δ : X _⦋n⦌) (i : Fin n) : (X.spine n Δ).a
rrow i = X.map (mkOfSucc i).op Δ
· 使用引理 `SSet.StrictSegal.spine_δ_arrow_lt`：spine_δ_arrow_lt (h : i.succ.castSucc
 < j) : (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `SSet.Subcomplex.yonedaEquiv_coe`：yonedaEquiv_coe {A : X.Subcomplex} {n :
 SimplexCategory} (f : stdSimplex.obj n ⟶ A) : (yonedaEquiv f).val = yonedaEquiv
 (f ≫ A.ι)
· 使用定理 `CategoryTheory.Subfunctor.lift_ι`：lift_ι : lift f hf ≫ G.ι = f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SSet.stdSimplex.map_apply`：map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁
 ⟶ m₂) {n : SimplexCategory} (x : (stdSimplex.{u}.obj n).obj m₁) : (stdSimplex.{
u}.obj n).map f…
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用引理 `SSet.yonedaEquiv_map`：yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m
) : yonedaEquiv.{u} (stdSimplex.map f) = stdSimplex.objEquiv.symm f
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `SimplexCategory.mkOfSucc_δ_lt`：mkOfSucc_δ_lt {n : Nat} {i : Fin n} {j : 
Fin (n + 2)} (h : i.succ.castSucc < j) : mkOfSucc i ≫ δ j = mkOfSucc i.castSucc
· 使用引理 `SSet.StrictSegal.spine_δ_arrow_gt`：spine_δ_arrow_gt (h : j < i.succ.cast
Succ) : (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ
· 使用引理 `SimplexCategory.mkOfSucc_δ_gt`：mkOfSucc_δ_gt {n : Nat} {i : Fin n} {j : 
Fin (n + 2)} (h : j < i.succ.castSucc) : mkOfSucc i ≫ δ j = mkOfSucc i.succ
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Any `StrictSegal` simplicial set is a `Quasicategory`.
-/
theorem quasicategory {X : SSet.{u}} (sx : StrictSegal X) : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
  use sx.spineToSimplex <| Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by lia
  · rw [← spine_arrow, spine_δ_arrow_lt sx _ hlt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, SSet.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, spine_δ_arrow_gt sx _ hgt]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, SSet.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_gt hgt]
    rfl
  · obtain _ | n := n
    · /- The only inner horn of `Δ[2]` does not contain the diagonal edge. -/
      obtain rfl : k = 0 := by omega
      fin_cases i <;> contradiction
    · /- We construct the triangle in the standard simplex as a 2-simplex in
      the horn. While the triangle is not contained in the inner horn `Λ[2, 1]`,
      it suffices to inhabit `Λ[n + 3, i] _⦋2⦌`. -/
      let triangle : (Λ[n + 3, i] : SSet.{u}) _⦋2⦌ :=
        horn.primitiveTriangle i h₀ hₙ k (by grind)
      /- The interval spanning from `k` to `k + 2` is equivalently the spine
      of the triangle with vertices `k`, `k + 1`, and `k + 2`. -/
      have hi : ((horn.spineId i h₀ hₙ).map σ₀).interval k 2 (by grind) =
          X.spine 2 (σ₀.app _ triangle) := by
        ext m
        dsimp [spine_arrow, Path.map_interval, Path.map_arrow]
        rw [← dsimp% σ₀.naturality_apply]
        apply congr_arg
        apply Subtype.ext
        ext a : 1
        fin_cases a <;> fin_cases m <;> rfl
      rw [← spine_arrow, spine_δ_arrow_eq sx _ heq, hi]
      simp only [spineToDiagonal, diagonal, spineToSimplex_spine_apply]
      rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality, types_comp_apply]
      dsimp
      apply congr_arg
      apply Subtype.ext
      ext z : 1
      dsimp [horn.face]
      rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
        Quiver.Hom.unop_op, stdSimplex.map_apply, Quiver.Hom.unop_op]
      dsimp [CosimplicialObject.δ]
      rw [SSet.yonedaEquiv_map]
      simp only [Equiv.apply_symm_apply, triangle]
      rw [mkOfSucc_δ_eq heq]
      fin_cases z <;> rfl

/-- Any simplicial set satisfying `IsStrictSegal` is a `Quasicategory`. -/
/-
**SSet.StrictSegal.quasicategory'** 是 Mathlib 中的一个实例，位于命名空间 `SSet.StrictSegal`。
形式化陈述：quasicategory' (X : SSet.{u}) [IsStrictSegal X] : Quasicategory X
参数：X : SSet.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.StrictSegal.quasicategory`：quasicategory {X : SSet.{u}} (sx : Stric
tSegal X) : Quasicategory X

--- 原说明 ---
Any simplicial set satisfying `IsStrictSegal` is a `Quasicategory`.
-/
instance quasicategory' (X : SSet.{u}) [IsStrictSegal X] : Quasicategory X :=
  quasicategory <| ofIsStrictSegal X

end SSet.StrictSegal

