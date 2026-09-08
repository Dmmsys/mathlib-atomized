/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Constructors for `Action V G` for some concrete categories

We construct `Action (Type*) G` from a `[MulAction G X]` instance and give some applications.
-/

@[expose] public section

assert_not_exists Field

universe u v

open CategoryTheory Limits

namespace TypeCat

/-
**TypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `TypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type u) : CoeFun (End X) (fun _ ↦ X → X) := (inferInstance : CoeFun (X ⟶ X) _)

/-- The group isomorphism between `Function.End X` and `CategoryTheory.End X`. -/
@[simps apply symm_apply]
/-
**TypeCat.endEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat`。
形式化陈述：endEquiv (X : Type u) : Function.End X ≃* End X where toFun f
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group isomorphism between `Function.End X` and `CategoryTheory.End X`.
-/
def endEquiv (X : Type u) : Function.End X ≃* End X where
  toFun f := ↾f
  invFun f := (ConcreteCategory.hom f : _ → _)
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  map_mul' := by aesop

end TypeCat

namespace Action

section
variable {G : Type u} [Group G] {A : Action (Type u) G}

@[simp]
/-
**Action.** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ρ_inv_self_apply (g : G) (x : A.V) :
    ConcreteCategory.hom ((A.ρ) g⁻¹) (ConcreteCategory.hom (A.ρ g) x) = x :=
  show ConcreteCategory.hom (A.ρ g⁻¹ * A.ρ g) x = x by simp [← map_mul]

@[simp]
/-
**Action.** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ρ_self_inv_apply (g : G) (x : A.V) :
    ConcreteCategory.hom (A.ρ g) (ConcreteCategory.hom (A.ρ g⁻¹) x) = x :=
  show ConcreteCategory.hom (A.ρ g * A.ρ g⁻¹) x = x by simp [← map_mul]

end

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
@[simps -isSimp]
/-
**Action.ofMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：ofMulAction (G : Type*) (H : Type u) [Monoid G] [MulAction G H] : Action (
Type u) G where V
参数：G : Type*；H : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundles a type `H` with a multiplicative action of `G` as an `Action`.
-/
def ofMulAction (G : Type*) (H : Type u) [Monoid G] [MulAction G H] :
    Action (Type u) G where
  V := H
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp (@MulAction.toEndHom _ _ _ (by assumption))

@[simp]
/-
**Action.ofMulAction_apply** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：ofMulAction_apply {G : Type*} {H : Type*} [Monoid G] [MulAction G H] (g : 
G) (x : H) : (ofMulAction G H).ρ g x = (g • x : H)
参数：g : G；x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulAction_apply {G : Type*} {H : Type*} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
/-
**Action.ofMulActionLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι -> 
Type max v u) [forall i : ι, MulAction G (F i)] : LimitCone (Discrete.functor fu
n i : ι => Action.ofMulAction G (F i)) where cone
参数：G : Type max v u；F : ι -> Type max v u；F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family `F` of types with `G`-actions, this is the limit cone demonstrati
ng that the
product of `F` as types is a product in the category of `G`-sets.
-/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i)) where
  cone :=
    { pt := Action.ofMulAction G (∀ i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨↾fun x => x i.as, fun _ => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := ↾fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact ConcreteCategory.congr_hom ((s.π.app ⟨j⟩).comm g) x }
      fac := fun _ _ => rfl
      uniq := fun s f h => by
        ext x
        funext j
        dsimp at *
        rw [← h ⟨j⟩]
        rfl }

/-- The `G`-set `G`, acting on itself by left multiplication. -/
/-
**Action.leftRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Action`。
形式化陈述：leftRegular (G : Type u) [Monoid G] : Action (Type u) G
参数：G : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `G`-set `G`, acting on itself by left multiplication.
-/
abbrev leftRegular (G : Type u) [Monoid G] : Action (Type u) G :=
  Action.ofMulAction G G

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
/-
**Action.diagonal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Action`。
形式化陈述：diagonal (G : Type u) [Monoid G] (n : Nat) : Action (Type u) G
参数：G : Type u；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `G`-set `Gⁿ`, acting on itself by left multiplication.
-/
abbrev diagonal (G : Type u) [Monoid G] (n : ℕ) : Action (Type u) G :=
  Action.ofMulAction G (Fin n → G)

/-- We have `Fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
/-
**Action.diagonalOneIsoLeftRegular** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：diagonalOneIsoLeftRegular (G : Type*) [Monoid G] : diagonal G 1 ≅ leftRegu
lar G
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have `Fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication.
-/
def diagonalOneIsoLeftRegular (G : Type*) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

namespace FintypeCat

/-- If `X` is a type with `[Fintype X]` and `G` acts on `X`, then `G` also acts on
`FintypeCat.of X`. -/
/-
**Action.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `Action.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a type with `[Fintype X]` and `G` acts on `X`, then `G` also acts on
`FintypeCat.of X`.
-/
instance (G : Type*) (X : Type*) [Monoid G] [MulAction G X] [Fintype X] :
    MulAction G (FintypeCat.of X) :=
  inferInstanceAs <| MulAction G X

/-- Bundles a finite type `H` with a multiplicative action of `G` as an `Action`. -/
/-
**Action.FintypeCat.ofMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Action.FintypeCat`。
形式化陈述：ofMulAction (G : Type*) (H : FintypeCat.{u}) [Monoid G] [MulAction G H] : 
Action FintypeCat G where V
参数：G : Type*；H : FintypeCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundles a finite type `H` with a multiplicative action of `G` as an `Action`.
-/
def ofMulAction (G : Type*) (H : FintypeCat.{u}) [Monoid G] [MulAction G H] :
    Action FintypeCat G where
  V := H
  ρ := InducedCategory.endEquiv.symm.toMonoidHom.comp <| (TypeCat.endEquiv _).toMonoidHom.comp
    MulAction.toEndHom

@[simp]
/-
**Action.FintypeCat.ofMulAction_apply** 是 Mathlib 中的一个定理，位于命名空间 `Action.FintypeC
at`。
形式化陈述：ofMulAction_apply {G : Type*} {H : FintypeCat.{u}} [Monoid G] [MulAction G
 H] (g : G) (x : H) : ConcreteCategory.hom ((FintypeCat.ofMulAction G H).ρ g) x 
= (g • x : H)
参数：g : G；x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulAction_apply {G : Type*} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
    (g : G) (x : H) : ConcreteCategory.hom ((FintypeCat.ofMulAction G H).ρ g) x = (g • x : H) :=
  rfl

section

/-- Shorthand notation for the quotient of `G` by `H` as a finite `G`-set. -/
notation:10 G:10 " ⧸ₐ " H:10 => Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H)

variable {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `N` is a normal subgroup of `G`, then this is the group homomorphism
sending an element `g` of `G` to the `G`-endomorphism of `G ⧸ₐ N` given by
multiplication with `g⁻¹` on the right. -/
/-
**Action.FintypeCat.toEndHom** 是 Mathlib 中的一个定义，位于命名空间 `Action.FintypeCat`。
形式化陈述：toEndHom [N.Normal] : G ->* End (G ⧸ₐ N) where toFun v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a normal subgroup of `G`, then this is the group homomorphism
sending an element `g` of `G` to the `G`-endomorphism of `G ⧸ₐ N` given by
multiplication with `g⁻¹` on the right.
-/
def toEndHom [N.Normal] : G →* End (G ⧸ₐ N) where
  toFun v :=
  { hom := FintypeCat.homMk (Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) <| fun a b h ↦ Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.leftRel_apply.mp h) _)
    comm := fun (g : G) ↦ by
      ext (x : G ⧸ N)
      induction x using Quotient.inductionOn with | h x
      dsimp
      apply (Quotient.lift_mk _ _ _).trans
      simp only [QuotientGroup.mk_mul, mul_assoc]
      rfl }
  map_one' := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    simp
  map_mul' σ τ := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn with | _ x
    change ⟦x * (σ * τ)⁻¹⟧ = ⟦x * τ⁻¹ * σ⁻¹⟧
    rw [mul_inv_rev, mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Action.FintypeCat.toEndHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Action.FintypeCat`
。
形式化陈述：toEndHom_apply [N.Normal] (g h : G) : (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma toEndHom_apply [N.Normal] (g h : G) : (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {N} in
/-
**Action.FintypeCat.toEndHom_trivial_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Action.Fi
ntypeCat`。
形式化陈述：toEndHom_trivial_of_mem [N.Normal] {n : G} (hn : n in N) : toEndHom N n = 
𝟙 (G ⧸ₐ N)
参数：hn : n in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.hom_ext`：hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom =
 φ₂.hom) : φ₁ = φ₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
lemma toEndHom_trivial_of_mem [N.Normal] {n : G} (hn : n ∈ N) : toEndHom N n = 𝟙 (G ⧸ₐ N) := by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction x using Quotient.inductionOn
  exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr <| by simpa)

/-- If `H` and `N` are subgroups of a group `G` with `N` normal, there is a canonical
group homomorphism `H ⧸ N ⊓ H` to the `G`-endomorphisms of `G ⧸ N`. -/
/-
**Action.FintypeCat.quotientToEndHom** 是 Mathlib 中的一个定义，位于命名空间 `Action.FintypeCa
t`。
形式化陈述：quotientToEndHom [N.Normal] : H ⧸ Subgroup.subgroupOf N H ->* End (G ⧸ₐ N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal

--- 原说明 ---
If `H` and `N` are subgroups of a group `G` with `N` normal, there is a canonica
l
group homomorphism `H ⧸ N ⊓ H` to the `G`-endomorphisms of `G ⧸ N`.
-/
def quotientToEndHom [N.Normal] : H ⧸ Subgroup.subgroupOf N H →* End (G ⧸ₐ N) :=
  QuotientGroup.lift (Subgroup.subgroupOf N H) ((toEndHom N).comp H.subtype) <| fun _ uinU' ↦
    toEndHom_trivial_of_mem uinU'

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Action.FintypeCat.quotientToEndHom_mk** 是 Mathlib 中的一个引理，位于命名空间 `Action.Fintyp
eCat`。
形式化陈述：quotientToEndHom_mk [N.Normal] (x : H) (g : G) : (quotientToEndHom H N ⟦x⟧
).hom ⟦g⟧ = ⟦g * x⁻¹⟧
参数：x : H；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal
-/
lemma quotientToEndHom_mk [N.Normal] (x : H) (g : G) :
    (quotientToEndHom H N ⟦x⟧).hom ⟦g⟧ = ⟦g * x⁻¹⟧ :=
  rfl

/-- If `N` and `H` are subgroups of a group `G` with `N ≤ H`, this is the canonical
`G`-morphism `G ⧸ N ⟶ G ⧸ H`. -/
/-
**Action.FintypeCat.quotientToQuotientOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Action.Fin
typeCat`。
形式化陈述：quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N <= H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H
) where hom
参数：G ⧸ H；h : N <= H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` and `H` are subgroups of a group `G` with `N ≤ H`, this is the canonical
`G`-morphism `G ⧸ N ⟶ G ⧸ H`.
-/
def quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N ≤ H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H) where
  hom := FintypeCat.homMk (Quotient.lift _ <| fun _ _ hab ↦ Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab))
  comm g := by
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    rfl

@[simp]
/-
**Action.FintypeCat.quotientToQuotientOfLE_hom_mk** 是 Mathlib 中的一个引理，位于命名空间 `Act
ion.FintypeCat`。
形式化陈述：quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N <= H) (x : G) : (qu
otientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧
参数：G ⧸ H；h : N <= H；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N ≤ H) (x : G) :
    (quotientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧ :=
  rfl

end

end FintypeCat

section ToMulAction

variable {V : Type (u + 1)} [LargeCategory V] {FV : V → V → Type*} {CV : V → Type*}
variable [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV]

/-
**Action.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：instMulAction {G : Type*} [Monoid G] (X : Action V G) : MulAction G (ToTyp
e X) where smul g x
参数：X : Action V G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction {G : Type*} [Monoid G] (X : Action V G) :
    MulAction G (ToType X) where
  smul g x := ConcreteCategory.hom (X.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.ρ 1) x = x
    simp
  mul_smul g h x := by
    change ConcreteCategory.hom (X.ρ (g * h)) x =
      ConcreteCategory.hom (X.ρ g) ((ConcreteCategory.hom (X.ρ h)) x)
    simp

/-- Specialize `instMulAction` to assist typeclass inference. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialize `instMulAction` to assist typeclass inference.
-/
instance {G : Type*} [Monoid G] (X : Action FintypeCat G) : MulAction G X.V :=
  Action.instMulAction X

end ToMulAction

end Action

