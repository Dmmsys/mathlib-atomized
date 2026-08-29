/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Limits in lattice categories are given by infimums and supremums.
-/

@[expose] public section


universe w w' u

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u} {J : Type w} [SmallCategory J] [FinCategory J]

/-- The limit cone over any functor from a finite diagram into a `SemilatticeInf` with `OrderTop`.
-/
@[simps]
/--
Definition of `finiteLimitCone` / `finiteLimitCone` 的定义

English:
definition finiteLimitCone
  signature: [SemilatticeInf α] [OrderTop α] (F : J ⥤ α)
  body: { pt := Finset.univ.inf F.obj
      π := { app := fun _ => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }

中文:
定义 finiteLimitCone
  签名: [SemilatticeInf α] [有顶序 α] (F : J ⥤ α)
  定义体: { pt := Finset.univ.inf F.obj
      π := { app := fun _ => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }

Depends on / 依赖: F.obj, Finset, Finset.inf_le, Finset.le_inf, Finset.univ.inf, Fintype, Fintype.complete, complete, down.down, homOfLE, inf_le, isLimit, le_inf
-/
def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := Finset.univ.inf F.obj
      π := { app := fun _ => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }

/--
The colimit cocone over any functor from a finite diagram into a `SemilatticeSup` with `OrderBot`.
-/
@[simps]
/--
Definition of `finiteColimitCocone` / `finiteColimitCocone` 的定义

English:
definition finiteColimitCocone
  signature: [SemilatticeSup α] [OrderBot α] (F : J ⥤ α)
  body: { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

中文:
定义 finiteColimitCocone
  签名: [SemilatticeSup α] [有底序 α] (F : J ⥤ α)
  定义体: { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

Depends on / 依赖: F.obj, Finset, Finset.le_sup, Finset.sup_le, Finset.univ.sup, Fintype, Fintype.complete, complete, down.down, homOfLE, isColimit, le_sup, sup_le
-/
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_colimit := fun F => HasColimit.mk (finiteColimitCocone F) }⟩

/--
theorem `finite_limit_eq_finset_univ_inf` / 定理 `finite_limit_eq_finset_univ_inf`

English:
theorem finite_limit_eq_finset_univ_inf
  given: [SemilatticeInf α] [OrderTop α] (F : J ⥤ α)
  proof: (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

中文:
定理 finite_limit_eq_finset_univ_inf
  条件: [SemilatticeInf α] [有顶序 α] (F : J ⥤ α)
  证明: (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, finiteLimitCone, isLimit, limit.isLimit, to_eq
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

/--
theorem `finite_colimit_eq_finset_univ_sup` / 定理 `finite_colimit_eq_finset_univ_sup`

English:
theorem finite_colimit_eq_finset_univ_sup
  given: [SemilatticeSup α] [OrderBot α] (F : J ⥤ α)
  proof: (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

中文:
定理 finite_colimit_eq_finset_univ_sup
  条件: [SemilatticeSup α] [有底序 α] (F : J ⥤ α)
  证明: (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, finiteColimitCocone, isColimit, to_eq
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

/--
theorem `finite_product_eq_finset_inf` / 定理 `finite_product_eq_finset_inf`

English:
theorem finite_product_eq_finset_inf
  statement: [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
  proof: by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

中文:
定理 finite_product_eq_finset_inf
  结论: [SemilatticeInf α] [有顶序 α] {ι : 类型u} [有限类型 ι]
  证明: by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

Depends on / 依赖: Discrete, Discrete.functor, Finset, Finset.inf_map, Finset.univ.inf, Finset.univ_map_equiv_to_embedding, Fintype, Fintype.elems.inf, IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, discreteEquiv, discreteEquiv.toEmbedding, finiteLimitCone, functor, inf_map, isLimit, limit.isLimit, toEmbedding, to_eq
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι -> α) : ∏ᶜ f = Finset.univ.inf f := by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

/--
theorem `finite_coproduct_eq_finset_sup` / 定理 `finite_coproduct_eq_finset_sup`

English:
theorem finite_coproduct_eq_finset_sup
  statement: [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
  proof: by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

中文:
定理 finite_coproduct_eq_finset_sup
  结论: [SemilatticeSup α] [有底序 α] {ι : 类型u} [有限类型 ι]
  证明: by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

Depends on / 依赖: Discrete, Discrete.functor, Finset, Finset.sup_map, Finset.univ.sup, Finset.univ_map_equiv_to_embedding, Fintype, Fintype.elems.sup, IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, discreteEquiv, discreteEquiv.toEmbedding, finiteColimitCocone, functor, isColimit, sup_map, toEmbedding
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι -> α) : ∐ f = Finset.univ.sup f := by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α := by
  have : forall x y : α, HasLimit (pair x y) := by
    let := hasFiniteLimits_of_hasFiniteLimits_of_size.{u} α
    infer_instance
  apply hasBinaryProducts_of_hasLimit_pair

/-- The binary product in the category of a `SemilatticeInf` with `OrderTop` is the same as the
infimum.
-/
@[simp]
/--
theorem `prod_eq_inf` / 定理 `prod_eq_inf`

English:
theorem prod_eq_inf
  given: [SemilatticeInf α] [OrderTop α] (x y : α)
  statement: Limits.prod x y = x ⊓ y
  proof: calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]

中文:
定理 prod_eq_inf
  条件: [SemilatticeInf α] [有顶序 α] (x y : α)
  结论: Limits.乘积 x y = x ⊓ y
  证明: calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]

Depends on / 依赖: Finset, Finset.univ.inf, Limits, Limits.prod, finite_limit_eq_finset_univ_inf
-/
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α := by
  have : forall x y : α, HasColimit (pair x y) := by
    let := hasFiniteColimits_of_hasFiniteColimits_of_size.{u} α
    infer_instance
  apply hasBinaryCoproducts_of_hasColimit_pair

/-- The binary coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
@[simp]
/--
theorem `coprod_eq_sup` / 定理 `coprod_eq_sup`

English:
theorem coprod_eq_sup
  given: [SemilatticeSup α] [OrderBot α] (x y : α)
  statement: Limits.coprod x y = x ⊔ y
  proof: calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: Finset.sup is realized as a fold, hence the definitional equality
    _ = x ⊔ y := by rw [sup_bot_eq]

中文:
定理 coprod_eq_sup
  条件: [SemilatticeSup α] [有底序 α] (x y : α)
  结论: Limits.coprod x y = x ⊔ y
  证明: calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: Finset.sup is realized as a fold, hence the definitional equality
    _ = x ⊔ y := by rw [sup_bot_eq]

Depends on / 依赖: Finset, Finset.univ.sup, Limits, Limits.coprod, colimit, coprod, finite_colimit_eq_finset_univ_sup
-/
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x y = x ⊔ y :=
  calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: Finset.sup is realized as a fold, hence the definitional equality
    _ = x ⊔ y := by rw [sup_bot_eq]

/-- The pullback in the category of a `SemilatticeInf` with `OrderTop` is the same as the infimum
over the objects.
-/
@[simp]
/--
theorem `pullback_eq_inf` / 定理 `pullback_eq_inf`

English:
theorem pullback_eq_inf
  given: [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z)
  proof: calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)

中文:
定理 pullback_eq_inf
  条件: [SemilatticeInf α] [有顶序 α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z)
  证明: calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)

Depends on / 依赖: Finset, Finset.univ.inf, cospan, f.le, finite_limit_eq_finset_univ_inf, inf_eq_right, inf_eq_right.mpr, inf_le_of_left_le, inf_top_eq, pullback
-/
theorem pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) :
    pullback f g = x ⊓ y :=
  calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)

/-- The pushout in the category of a `SemilatticeSup` with `OrderBot` is the same as the supremum
over the objects.
-/
@[simp]
/--
theorem `pushout_eq_sup` / 定理 `pushout_eq_sup`

English:
theorem pushout_eq_sup
  given: [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y)
  proof: calc
    pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)

中文:
定理 pushout_eq_sup
  条件: [SemilatticeSup α] [有底序 α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y)
  证明: calc
    pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)

Depends on / 依赖: Finset, Finset.univ.sup, colimit, f.le, finite_colimit_eq_finset_univ_sup, le_sup_of_le_left, pushout, sup_bot_eq, sup_eq_right, sup_eq_right.mpr
-/
theorem pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) :
    pushout f g = x ⊔ y :=
  calc
    pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)

end Semilattice

variable {α : Type u} [CompleteLattice α] {J : Type w} [Category.{w'} J]

/-- The limit cone over any functor into a complete lattice.
-/
@[simps]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: (F : J ⥤ α)
  body: { pt := iInf F.obj
      π := { app := fun _ => homOfLE (sInf_le (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (le_sInf (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }

中文:
定义 limitCone
  签名: (F : J ⥤ α)
  定义体: { pt := iInf F.obj
      π := { app := fun _ => homOfLE (sInf_le (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (le_sInf (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }

Depends on / 依赖: F.obj, Set.mem_range_self, homOfLE, isLimit, le_sInf, mem_range_self, sInf_le
-/
def limitCone (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := iInf F.obj
      π := { app := fun _ => homOfLE (sInf_le (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (le_sInf (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }

/-- The colimit cocone over any functor into a complete lattice.
-/
@[simps]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: (F : J ⥤ α)
  body: { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

中文:
定义 colimitCocone
  签名: (F : J ⥤ α)
  定义体: { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

Depends on / 依赖: F.obj, Set.mem_range_self, homOfLE, isColimit, le_sSup, mem_range_self, sSup_le
-/
def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

-- see Note [lower instance priority]
instance (priority := 100) hasLimits_of_completeLattice : HasLimitsOfSize.{w, w'} α where
  has_limits_of_shape _ := { has_limit := fun F => HasLimit.mk (limitCone F) }

-- see Note [lower instance priority]
instance (priority := 100) hasColimits_of_completeLattice : HasColimitsOfSize.{w, w'} α where
  has_colimits_of_shape _ := { has_colimit := fun F => HasColimit.mk (colimitCocone F) }

/--
theorem `limit_eq_iInf` / 定理 `limit_eq_iInf`

English:
theorem limit_eq_iInf
  given: (F : J ⥤ α)
  statement: limit F = iInf F.obj
  proof: (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq

中文:
定理 limit_eq_iInf
  条件: (F : J ⥤ α)
  结论: limit F = iInf F.obj
  证明: (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, limitCone, to_eq
-/
theorem limit_eq_iInf (F : J ⥤ α) : limit F = iInf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq

/--
theorem `colimit_eq_iSup` / 定理 `colimit_eq_iSup`

English:
theorem colimit_eq_iSup
  given: (F : J ⥤ α)
  statement: colimit F = iSup F.obj
  proof: (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq

中文:
定理 colimit_eq_iSup
  条件: (F : J ⥤ α)
  结论: colimit F = iSup F.obj
  证明: (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitCocone, isColimit, to_eq
-/
theorem colimit_eq_iSup (F : J ⥤ α) : colimit F = iSup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq

end CategoryTheory.Limits.CompleteLattice
