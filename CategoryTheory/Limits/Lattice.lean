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
/-
**CategoryTheory.Limits.CompleteLattice.finiteLimitCone** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F 
where cone
参数：F : J ⥤ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone over any functor from a finite diagram into a `SemilatticeInf` wi
th `OrderTop`.
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
/-
**CategoryTheory.Limits.CompleteLattice.finiteColimitCocone** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitC
ocone F where cocone
参数：F : J ⥤ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone over any functor from a finite diagram into a `SemilatticeSup
` with `OrderBot`.
-/
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_colimit := fun F => HasColimit.mk (finiteColimitCocone F) }⟩

/-- The limit of a functor from a finite diagram into a `SemilatticeInf` with `OrderTop` is the
infimum of the objects in the image.
-/
/-
**CategoryTheory.Limits.CompleteLattice.finite_limit_eq_finset_univ_inf** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α
) : limit F = Finset.univ.inf F.obj
参数：F : J ⥤ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α

--- 原说明 ---
The limit of a functor from a finite diagram into a `SemilatticeInf` with `Order
Top` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

/-- The colimit of a functor from a finite diagram into a `SemilatticeSup` with `OrderBot`
is the supremum of the objects in the image.
-/
/-
**CategoryTheory.Limits.CompleteLattice.finite_colimit_eq_finset_univ_sup** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤
 α) : colimit F = Finset.univ.sup F.obj
参数：F : J ⥤ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSu
p_orderBot`：∀ {α : Type u} [inst : SemilatticeSup α] [OrderBot α], CategoryTheor
y.Limits.HasFiniteColimits α

--- 原说明 ---
The colimit of a functor from a finite diagram into a `SemilatticeSup` with `Ord
erBot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

/--
A finite product in the category of a `SemilatticeInf` with `OrderTop` is the same as the infimum.
-/
/-
**CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} 
[Fintype ι] (f : ι -> α) : ∏ᶜ f = Finset.univ.inf f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.univ_map_equiv_to_embedding`：univ_map_equiv_to_embedding {α β : T
ype*} [Fintype α] [Fintype β] (e : α ≃ β) : univ.map e.toEmbedding = univ

--- 原说明 ---
A finite product in the category of a `SemilatticeInf` with `OrderTop` is the sa
me as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∏ᶜ f = Finset.univ.inf f := by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

/-- A finite coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
/-
**CategoryTheory.Limits.CompleteLattice.finite_coproduct_eq_finset_sup** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u
} [Fintype ι] (f : ι -> α) : ∐ f = Finset.univ.sup f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSu
p_orderBot`：∀ {α : Type u} [inst : SemilatticeSup α] [OrderBot α], CategoryTheor
y.Limits.HasFiniteColimits α
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.univ_map_equiv_to_embedding`：univ_map_equiv_to_embedding {α β : T
ype*} [Fintype α] [Fintype β] (e : α ≃ β) : univ.map e.toEmbedding = univ

--- 原说明 ---
A finite coproduct in the category of a `SemilatticeSup` with `OrderBot` is the 
same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∐ f = Finset.univ.sup f := by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α := by
  have : ∀ x y : α, HasLimit (pair x y) := by
    let := hasFiniteLimits_of_hasFiniteLimits_of_size.{u} α
    infer_instance
  apply hasBinaryProducts_of_hasLimit_pair

/-- The binary product in the category of a `SemilatticeInf` with `OrderTop` is the same as the
infimum.
-/
@[simp]
/-
**CategoryTheory.Limits.CompleteLattice.prod_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.CompleteLattice`。
形式化陈述：prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = 
x ⊓ y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.instHasBinaryProductsOfOrderTop`：∀
 {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.Limits.HasB
inaryProducts α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finite_limit_eq_finset_univ_inf`：f
inite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : lim
it F = Finset.univ.inf F.obj
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a

--- 原说明 ---
The binary product in the category of a `SemilatticeInf` with `OrderTop` is the 
same as the
infimum.
-/
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α := by
  have : ∀ x y : α, HasColimit (pair x y) := by
    let := hasFiniteColimits_of_hasFiniteColimits_of_size.{u} α
    infer_instance
  apply hasBinaryCoproducts_of_hasColimit_pair

/-- The binary coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
@[simp]
/-
**CategoryTheory.Limits.CompleteLattice.coprod_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.CompleteLattice`。
形式化陈述：coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x 
y = x ⊔ y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.instHasBinaryCoproductsOfOrderBot`
：∀ {α : Type u} [inst : SemilatticeSup α] [OrderBot α], CategoryTheory.Limits.Ha
sBinaryCoproducts α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSu
p_orderBot`：∀ {α : Type u} [inst : SemilatticeSup α] [OrderBot α], CategoryTheor
y.Limits.HasFiniteColimits α
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finite_colimit_eq_finset_univ_sup`
：finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
 colimit F = Finset.univ.sup F.obj
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a

--- 原说明 ---
The binary coproduct in the category of a `SemilatticeSup` with `OrderBot` is th
e same as the
supremum.
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
/-
**CategoryTheory.Limits.CompleteLattice.pullback_eq_inf** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g
 : y ⟶ z) : pullback f g = x ⊓ y
参数：f : x ⟶ z；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finite_limit_eq_finset_univ_inf`：f
inite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : lim
it F = Finset.univ.inf F.obj
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c

--- 原说明 ---
The pullback in the category of a `SemilatticeInf` with `OrderTop` is the same a
s the infimum
over the objects.
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
/-
**CategoryTheory.Limits.CompleteLattice.pushout_eq_sup** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g 
: z ⟶ y) : pushout f g = x ⊔ y
参数：x y z : α；f : z ⟶ x；g : z ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSu
p_orderBot`：∀ {α : Type u} [inst : SemilatticeSup α] [OrderBot α], CategoryTheor
y.Limits.HasFiniteColimits α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finite_colimit_eq_finset_univ_sup`
：finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
 colimit F = Finset.univ.sup F.obj
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b

--- 原说明 ---
The pushout in the category of a `SemilatticeSup` with `OrderBot` is the same as
 the supremum
over the objects.
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
/-
**CategoryTheory.Limits.CompleteLattice.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.CompleteLattice`。
形式化陈述：limitCone (F : J ⥤ α) : LimitCone F where cone
参数：F : J ⥤ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone over any functor into a complete lattice.
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
/-
**CategoryTheory.Limits.CompleteLattice.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.CompleteLattice`。
形式化陈述：colimitCocone (F : J ⥤ α) : ColimitCocone F where cocone
参数：F : J ⥤ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone over any functor into a complete lattice.
-/
def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (le_sSup (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (sSup_le (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasLimits_of_completeLattice : HasLimitsOfSize.{w, w'} α where
  has_limits_of_shape _ := { has_limit := fun F => HasLimit.mk (limitCone F) }

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasColimits_of_completeLattice : HasColimitsOfSize.{w, w'} α where
  has_colimits_of_shape _ := { has_colimit := fun F => HasColimit.mk (colimitCocone F) }

/-- The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
/-
**CategoryTheory.Limits.CompleteLattice.limit_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.CompleteLattice`。
形式化陈述：limit_eq_iInf (F : J ⥤ α) : limit F = iInf F.obj
参数：F : J ⥤ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice`：∀ {α
 : Type u} [inst : CompleteLattice α], CategoryTheory.Limits.HasLimitsOfSize.{w,
 w', u, u} α

--- 原说明 ---
The limit of a functor into a complete lattice is the infimum of the objects in 
the image.
-/
theorem limit_eq_iInf (F : J ⥤ α) : limit F = iInf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq

/-- The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
/-
**CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：colimit_eq_iSup (F : J ⥤ α) : colimit F = iSup F.obj
参数：F : J ⥤ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasColimits_of_completeLattice`：∀ 
{α : Type u} [inst : CompleteLattice α], CategoryTheory.Limits.HasColimitsOfSize
.{w, w', u, u} α

--- 原说明 ---
The colimit of a functor into a complete lattice is the supremum of the objects 
in the image.
-/
theorem colimit_eq_iSup (F : J ⥤ α) : colimit F = iSup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq

end CategoryTheory.Limits.CompleteLattice

