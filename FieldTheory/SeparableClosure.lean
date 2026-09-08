/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!

# Separable closure

This file contains basics about the (relative) separable closure of a field extension.

## Main definitions

- `separableClosure`: the relative separable closure of `F` in `E`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

- `SeparableClosure`: the absolute separable closure, defined to be the relative separable
  closure inside the algebraic closure.

- `Field.sepDegree F E`: the (infinite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `separableClosure F E / F`. Later we will show
  that (`Field.finSepDegree_eq`, not in this file), if `Field.Emb F E` is finite, then this
  coincides with `Field.finSepDegree F E`.

- `Field.insepDegree F E`: the (infinite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E`.

- `Field.finInsepDegree F E`: the finite inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E` as a natural number.
  It is zero if such field extension is not finite.

## Main results

- `le_separableClosure_iff`: an intermediate field of `E / F` is contained in the
  separable closure of `F` in `E` if and only if it is separable over `F`.

- `separableClosure.normalClosure_eq_self`: the normal closure of the separable
  closure of `F` in `E` is equal to itself.

- `separableClosure.isGalois`: the separable closure in a normal extension is Galois
  (namely, normal and separable).

- `separableClosure.isSepClosure`: the separable closure in a separably closed extension
  is a separable closure of the base field.

- `IntermediateField.isSeparable_adjoin_iff_isSeparable`: `F(S) / F` is a separable extension if and
  only if all elements of `S` are separable elements.

- `separableClosure.eq_top_iff`: the separable closure of `F` in `E` is equal to `E`
  if and only if `E / F` is separable.

## Tags

separable degree, degree, separable closure

-/

@[expose] public section

assert_not_exists IsGalois

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section separableClosure

/-- The (relative) separable closure of `F` in `E`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
@[stacks 09HC]
/-
**separableClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：separableClosure : IntermediateField F E where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.isSeparable_mul`：isSeparable_mul {x y : E} (hx : IsSeparable F x) 
(hy : IsSeparable F y) : IsSeparable F (x * y)
· 使用定理 `Field.isSeparable_add`：isSeparable_add {x y : E} (hx : IsSeparable F x) 
(hy : IsSeparable F y) : IsSeparable F (x + y)
· 使用定理 `Field.isSeparable_inv`：isSeparable_inv {x : E} (hx : IsSeparable F x) : 
IsSeparable F x⁻¹

--- 原说明 ---
The (relative) separable closure of `F` in `E`, or called maximal separable sube
xtension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
 separable
elements. The previous results prove that these elements are closed under field 
operations.
-/
def separableClosure : IntermediateField F E where
  carrier := {x | IsSeparable F x}
  mul_mem' := isSeparable_mul
  add_mem' := isSeparable_add
  algebraMap_mem' := isSeparable_algebraMap
  inv_mem' _ := isSeparable_inv

variable {F E K}

/-- An element is contained in the separable closure of `F` in `E` if and only if
it is a separable element. -/
/-
**mem_separableClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_separableClosure_iff {x : E} : x in separableClosure F E ↔ IsSeparable
 F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is contained in the separable closure of `F` in `E` if and only if
it is a separable element.
-/
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ IsSeparable F x := Iff.rfl

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`separableClosure F K` if and only if `x` is contained in `separableClosure F E`. -/
/-
**map_mem_separableClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_separableClosure_iff (i : E ->ₐ[F] K) {x : E} : i x in separableCl
osure F K ↔ x in separableClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained i
n
`separableClosure F K` if and only if `x` is contained in `separableClosure F E`
.
-/
theorem map_mem_separableClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ separableClosure F K ↔ x ∈ separableClosure F E := by
  simp_rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq i i.injective]

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`separableClosure F K` under the map `i` is equal to `separableClosure F E`. -/
/-
**separableClosure.comap_eq_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.comap_eq_of_algHom (i : E ->ₐ[F] K) : (separableClosure F
 K).comap i = separableClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `map_mem_separableClosure_iff`：map_mem_separableClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in separableClosure F K ↔ x in separableClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`separableClosure F K` under the map `i` is equal to `separableClosure F E`.
-/
theorem separableClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F K).comap i = separableClosure F E := by
  ext x
  exact map_mem_separableClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `separableClosure F E`
under the map `i` is contained in `separableClosure F K`. -/
/-
**separableClosure.map_le_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.map_le_of_algHom (i : E ->ₐ[F] K) : (separableClosure F E
).map i <= separableClosure F K
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.map_le_iff_le_comap`：map_le_iff_le_comap {f : L ->ₐ[K]
 L'} {s : IntermediateField K L} {t : IntermediateField K L'} : s.map f <= t ↔ s
 <= t.comap f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `separableClosure.comap_eq_of_algHom`：separableClosure.comap_eq_of_algHom
 (i : E ->ₐ[F] K) : (separableClosure F K).comap i = separableClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `separa
bleClosure F E`
under the map `i` is contained in `separableClosure F K`.
-/
theorem separableClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (separableClosure F E).map i ≤ separableClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/-- If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial separable
subextensions (when `K / E` is algebraic, this means that it is purely inseparable),
then the image of `separableClosure F E` in `K` is equal to `separableClosure F K`. -/
/-
**separableClosure.map_eq_of_separableClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：separableClosure.map_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalar
Tower F E K] (h : separableClosure E K = ⊥) : (separableClosure F E).map (IsScal
arTower.toAlgHom F E K) = separableClosure F K
参数：h : separableClosure E K = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `separableClosure.map_le_of_algHom`：separableClosure.map_le_of_algHom (i 
: E ->ₐ[F] K) : (separableClosure F E).map i <= separableClosure F K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `map_mem_separableClosure_iff`：map_mem_separableClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in separableClosure F K ↔ x in separableClosure F E

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial 
separable
subextensions (when `K / E` is algebraic, this means that it is purely inseparab
le),
then the image of `separableClosure F E` in `K` is equal to `separableClosure F 
K`.
-/
theorem separableClosure.map_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : separableClosure E K = ⊥) :
    (separableClosure F E).map (IsScalarTower.toAlgHom F E K) = separableClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_separableClosure_iff.2
    (IsSeparable.tower_top E <| mem_separableClosure_iff.1 hx)
  exact ⟨y, (map_mem_separableClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `separableClosure F E`
under the map `i` is equal to `separableClosure F K`. -/
/-
**separableClosure.map_eq_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) : (separableClosure F 
E).map i = separableClosure F K
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `separableClosure.map_le_of_algHom`：separableClosure.map_le_of_algHom (i 
: E ->ₐ[F] K) : (separableClosure F E).map i <= separableClosure F K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_mem_separableClosure_iff`：map_mem_separableClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in separableClosure F K ↔ x in separableClosure F E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `separabl
eClosure F E`
under the map `i` is equal to `separableClosure F K`.
-/
theorem separableClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (separableClosure F E).map i = separableClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_separableClosure_iff i.symm).2 h, by simp⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `separableClosure F E` and
`separableClosure F K` are also isomorphic as `F`-algebras. -/
/-
**separableClosure.algEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) : separableClosure F E
 ≃ₐ[F] separableClosure F K
参数：i : E ≃ₐ[F] K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `separableClosure.map_eq_of_algEquiv`：separableClosure.map_eq_of_algEquiv
 (i : E ≃ₐ[F] K) : (separableClosure F E).map i = separableClosure F K

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then `separableClosure F E` and
`separableClosure F K` are also isomorphic as `F`-algebras.
-/
def separableClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    separableClosure F E ≃ₐ[F] separableClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.separableClosure := separableClosure.algEquivOfAlgEquiv

variable (F E K)

/-- The separable closure of `F` in `E` is algebraic over `F`. -/
/-
**separableClosure.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isAlgebraic_iff`：isAlgebraic_iff {x : S} : IsAlgebraic
 K x ↔ IsAlgebraic K (x : L)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The separable closure of `F` in `E` is algebraic over `F`.
-/
instance separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  ⟨fun x ↦ isAlgebraic_iff.2 (IsSeparable.isIntegral x.2).isAlgebraic⟩

/-- The separable closure of `F` in `E` is separable over `F`. -/
@[stacks 030K "$E_{sep}/F$ is separable"]
/-
**separableClosure.isSeparable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：separableClosure.isSeparable : Algebra.IsSeparable F (separableClosure F E
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The separable closure of `F` in `E` is separable over `F`.
-/
instance separableClosure.isSeparable : Algebra.IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ by simpa only [IsSeparable, minpoly_eq] using! x.2⟩

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if all of its elements are separable over `F`. -/
/-
**le_separableClosure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_separableClosure' {L : IntermediateField F E} (hs : forall x : L, IsSep
arable F x) : L <= separableClosure F E
参数：hs : forall x : L, IsSeparable F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)

--- 原说明 ---
An intermediate field of `E / F` is contained in the separable closure of `F` in
 `E`
if all of its elements are separable over `F`.
-/
theorem le_separableClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsSeparable F x) :
    L ≤ separableClosure F E := fun x h ↦ by simpa only [IsSeparable, minpoly_eq] using! hs ⟨x, h⟩

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if it is separable over `F`. -/
/-
**le_separableClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] 
: L <= separableClosure F E
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_separableClosure'`：le_separableClosure' {L : IntermediateField F E} (
hs : forall x : L, IsSeparable F x) : L <= separableClosure F E
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
An intermediate field of `E / F` is contained in the separable closure of `F` in
 `E`
if it is separable over `F`.
-/
theorem le_separableClosure (L : IntermediateField F E) [Algebra.IsSeparable F L] :
    L ≤ separableClosure F E := le_separableClosure' F E (Algebra.IsSeparable.isSeparable F)

/-- An intermediate field of `E / F` is contained in the separable closure of `F` in `E`
if and only if it is separable over `F`. -/
/-
**le_separableClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_separableClosure_iff (L : IntermediateField F E) : L <= separableClosur
e F E ↔ Algebra.IsSeparable F L
参数：L : IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Subalgebra.isSeparable_iff`：Subalgebra.isSeparable_iff [Ring L] [Algebra
 F L] {S : Subalgebra F L} : Algebra.IsSeparable F S ↔ forall x in S, IsSeparabl
e F x

--- 原说明 ---
An intermediate field of `E / F` is contained in the separable closure of `F` in
 `E`
if and only if it is separable over `F`.
-/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ Algebra.IsSeparable F L :=
  Subalgebra.isSeparable_iff.symm

/-- The separable closure in `E` of the separable closure of `F` in `E` is equal to itself. -/
/-
**separableClosure.separableClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.separableClosure_eq_bot : separableClosure (separableClos
ure F E) E = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `IsSeparable.of_algebra_isSeparable_of_isSeparable`：IsSeparable.of_algebr
a_isSeparable_of_isSeparable [Algebra E K] [IsScalarTower F E K] [Algebra.IsSepa
rable F E] {x : K} (hsep : IsSeparable …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x

--- 原说明 ---
The separable closure in `E` of the separable closure of `F` in `E` is equal to 
itself.
-/
theorem separableClosure.separableClosure_eq_bot :
    separableClosure (separableClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, IsSeparable.of_algebra_isSeparable_of_isSeparable F (mem_separableClosure_iff.1 hx)⟩, rfl⟩

/-- The normal closure in `E/F` of the separable closure of `F` in `E` is equal to itself. -/
/-
**separableClosure.normalClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.normalClosure_eq_self : normalClosure F (separableClosure
 F E) E = separableClosure F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `normalClosure_le_iff`：normalClosure_le_iff {K' : IntermediateField F L} 
: normalClosure F K L <= K' ↔ forall f : K ->ₐ[F] L, f.fieldRange <= K'
· 使用定理 `AlgEquiv.Algebra.isSeparable`：AlgEquiv.Algebra.isSeparable [Algebra.IsSe
parable F K] : Algebra.IsSeparable F E
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `le_separableClosure`：le_separableClosure (L : IntermediateField F E) [Al
gebra.IsSeparable F L] : L <= separableClosure F E
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L

--- 原说明 ---
The normal closure in `E/F` of the separable closure of `F` in `E` is equal to i
tself.
-/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    have : Algebra.IsSeparable F i.fieldRange :=
      (AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i))
    le_separableClosure F E _) (le_normalClosure _)

/-- `F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements. -/
/-
**IntermediateField.isSeparable_adjoin_iff_isSeparable** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IntermediateField.isSeparable_adjoin_iff_isSeparable {S : Set E} : Algebra
.IsSeparable F (adjoin F S) ↔ forall x in S, IsSeparable F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_separableClosure_iff`：le_separableClosure_iff (L : IntermediateField 
F E) : L <= separableClosure F E ↔ Algebra.IsSeparable F L
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T

--- 原说明 ---
`F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements.
-/
theorem IntermediateField.isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, IsSeparable F x :=
  (le_separableClosure_iff F E _).symm.trans adjoin_le_iff

/-- If `p` is a separable polynomial with splitting field `E` over `F`, then `E / F` is a
separable extension. -/
/-
**Algebra.isSeparable_of_separable_splitting_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_of_separable_splitting_field {p : F[X]} [sp : p.IsSpli
ttingField F E] (hp : p.Separable) : Algebra.IsSeparable F E
参数：hp : p.Separable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.isSeparable_top`：isSeparable_top : Algebra.IsSeparable
 F (⊤ : IntermediateField F E) ↔ Algebra.IsSeparable F E
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSplittingField_iff_intermediateField`：isSplittingField_iff_intermediat
eField : p.IsSplittingField K L ↔ (p.map (algebraMap K L)).Splits ∧ Intermediate
Field.adjoin K (p.rootSet L)…
· 使用定理 `IntermediateField.isSeparable_adjoin_iff_isSeparable`：IntermediateField.
isSeparable_adjoin_iff_isSeparable {S : Set E} : Algebra.IsSeparable F (adjoin F
 S) ↔ forall x in S, IsSeparable F x
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.aeval_eq_zero_of_mem_rootSet`：aeval_eq_zero_of_mem_rootSet {p
 : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S} (hx : a in p.rootSet S)
 : aeval a p = 0

--- 原说明 ---
If `p` is a separable polynomial with splitting field `E` over `F`, then `E / F`
 is a
separable extension.
-/
theorem Algebra.isSeparable_of_separable_splitting_field {p : F[X]}
    [sp : p.IsSplittingField F E] (hp : p.Separable) : Algebra.IsSeparable F E := by
  rw [← isSeparable_top, ← (isSplittingField_iff_intermediateField.mp sp).2,
    isSeparable_adjoin_iff_isSeparable]
  exact fun x hx ↦ hp.of_dvd (minpoly.dvd F x (aeval_eq_zero_of_mem_rootSet hx))

/-- The separable closure of `F` in `E` is equal to `E` if and only if `E / F` is
separable. -/
/-
**separableClosure.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ Algebra.IsSeparab
le F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_separableClosure_iff`：mem_separableClosure_iff {x : E} : x in separa
bleClosure F E ↔ IsSeparable F x
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x

--- 原说明 ---
The separable closure of `F` in `E` is equal to `E` if and only if `E / F` is
separable.
-/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ Algebra.IsSeparable F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_separableClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_separableClosure_iff.2 (Algebra.IsSeparable.isSeparable _ x)⟩

/-- If `K / E / F` is a field extension tower, then `separableClosure F K` is contained in
`separableClosure E K`. -/
/-
**separableClosure.le_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] : 
separableClosure F K <= (separableClosure E K).restrictScalars F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x

--- 原说明 ---
If `K / E / F` is a field extension tower, then `separableClosure F K` is contai
ned in
`separableClosure E K`.
-/
theorem separableClosure.le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    separableClosure F K ≤ (separableClosure E K).restrictScalars F :=
  fun _ ↦ IsSeparable.tower_top E

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable, then
`separableClosure F K` is equal to `separableClosure E K`. -/
/-
**separableClosure.eq_restrictScalars_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalar
Tower F E K] [Algebra.IsSeparable F E] : separableClosure F K = (separableClosur
e E K).restrictScalars F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `separableClosure.le_restrictScalars`：separableClosure.le_restrictScalars
 [Algebra E K] [IsScalarTower F E K] : separableClosure F K <= (separableClosure
 E K).restrictScalars F
· 使用定理 `IsSeparable.of_algebra_isSeparable_of_isSeparable`：IsSeparable.of_algebr
a_isSeparable_of_isSeparable [Algebra E K] [IsScalarTower F E K] [Algebra.IsSepa
rable F E] {x : K} (hsep : IsSeparable …

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is separable, then
`separableClosure F K` is equal to `separableClosure E K`.
-/
theorem separableClosure.eq_restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] : separableClosure F K = (separableClosure E K).restrictScalars F :=
  (separableClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    IsSeparable.of_algebra_isSeparable_of_isSeparable F h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `separableClosure F K` is contained
in `separableClosure E K`. -/
/-
**separableClosure.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] : adjoin E 
(separableClosure F K) <= separableClosure E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `separableClosure.le_restrictScalars`：separableClosure.le_restrictScalars
 [Algebra E K] [IsScalarTower F E K] : separableClosure F K <= (separableClosure
 E K).restrictScalars F

--- 原说明 ---
If `K / E / F` is a field extension tower, then `E` adjoin `separableClosure F K
` is contained
in `separableClosure E K`.
-/
theorem separableClosure.adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (separableClosure F K) ≤ separableClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

/-- A compositum of two separable extensions is separable. -/
/-
**IntermediateField.isSeparable_sup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E) [h1 : Al
gebra.IsSeparable F L1] [h2 : Algebra.IsSeparable F L2] : Algebra.IsSeparable F 
(L1 ⊔ L2 : IntermediateField F E)
参数：L1 L2 : IntermediateField F E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_separableClosure_iff`：le_separableClosure_iff (L : IntermediateField 
F E) : L <= separableClosure F E ↔ Algebra.IsSeparable F L
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c

--- 原说明 ---
A compositum of two separable extensions is separable.
-/
instance IntermediateField.isSeparable_sup (L1 L2 : IntermediateField F E)
    [h1 : Algebra.IsSeparable F L1] [h2 : Algebra.IsSeparable F L2] :
    Algebra.IsSeparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_separableClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of separable extensions is separable. -/
/-
**IntermediateField.isSeparable_iSup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IntermediateField.isSeparable_iSup {ι : Type*} {t : ι -> IntermediateField
 F E} [h : forall i, Algebra.IsSeparable F (t i)] : Algebra.IsSeparable F (⨆ i, 
t i : IntermediateField F E)
参数：t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
A compositum of separable extensions is separable.
-/
instance IntermediateField.isSeparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, Algebra.IsSeparable F (t i)] :
    Algebra.IsSeparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_separableClosure_iff] at h ⊢
  exact iSup_le h

variable {F E} in
/-
**le_restrictScalars_separableClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_restrictScalars_separableClosure (L : IntermediateField F E) : L <= (se
parableClosure L E).restrictScalars F
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isSeparable_algebraMap`：isSeparable_algebraMap (x : F) : IsSeparable F (
algebraMap F K x)
-/
theorem le_restrictScalars_separableClosure (L : IntermediateField F E) :
    L ≤ (separableClosure L E).restrictScalars F :=
  fun x hx ↦ isSeparable_algebraMap (F := L) ⟨x, hx⟩

/-- `separableClosure` as a `ClosureOperator`. -/
/-
**separableClosureOperator** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：separableClosureOperator : ClosureOperator (IntermediateField F E)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `le_restrictScalars_separableClosure`：le_restrictScalars_separableClosure
 (L : IntermediateField F E) : L <= (separableClosure L E).restrictScalars F

--- 原说明 ---
`separableClosure` as a `ClosureOperator`.
-/
abbrev separableClosureOperator : ClosureOperator (IntermediateField F E) := by
  refine .mk' (fun K ↦ (separableClosure K E).restrictScalars F) (fun K L le x hx ↦ ?_)
    le_restrictScalars_separableClosure fun K x hx ↦ ?_
  · let _ := (inclusion le).toAlgebra
    have : IsScalarTower K L E := .of_algebraMap_eq' rfl
    exact hx.tower_top _
  · obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2
/-
**isClosed_restrictScalars_separableClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_restrictScalars_separableClosure [Algebra K E] [IsScalarTower F K
 E] : (separableClosureOperator F E).IsClosed ((separableClosure K E).restrictSc
alars F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.isClosed_iff_closure_le`：isClosed_iff_closure_le : c.IsC
losed x ↔ c x <= x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `separableClosure.separableClosure_eq_bot`：separableClosure.separableClos
ure_eq_bot : separableClosure (separableClosure F E) E = ⊥
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma isClosed_restrictScalars_separableClosure [Algebra K E] [IsScalarTower F K E] :
    (separableClosureOperator F E).IsClosed ((separableClosure K E).restrictScalars F) :=
  ClosureOperator.isClosed_iff_closure_le.mpr fun x hx ↦ by
    obtain ⟨x, rfl⟩ := (separableClosure.separableClosure_eq_bot K E).le hx
    exact x.2
/-
**separableClosure_le_separableClosure_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：separableClosure_le_separableClosure_iff [Algebra K E] [IsScalarTower F K 
E] {L : IntermediateField F E} : (separableClosure L E).restrictScalars F <= (se
parableClosure K E).restrictScalars F ↔ L <= (separableClosure K E).restrictScal
ars F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
· 使用引理 `isClosed_restrictScalars_separableClosure`：isClosed_restrictScalars_sepa
rableClosure [Algebra K E] [IsScalarTower F K E] : (separableClosureOperator F E
).IsClosed ((separableClosure K…
-/
lemma separableClosure_le_separableClosure_iff
    [Algebra K E] [IsScalarTower F K E] {L : IntermediateField F E} :
    (separableClosure L E).restrictScalars F ≤ (separableClosure K E).restrictScalars F ↔
      L ≤ (separableClosure K E).restrictScalars F :=
  (isClosed_restrictScalars_separableClosure F E K).closure_le_iff

end separableClosure

namespace Field

/-- The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `separableClosure F E / F`. -/
@[stacks 030L "Part 1"]
/-
**Field.sepDegree** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：sepDegree
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `separableClosure F E / F`.
-/
def sepDegree := Module.rank F (separableClosure F E)

/-- The (infinite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E`. -/
@[stacks 030L "Part 2"]
/-
**Field.insepDegree** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：insepDegree
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (infinite) inseparable degree for a general field extension `E / F` is defin
ed
to be the degree of `E / separableClosure F E`.
-/
def insepDegree := Module.rank (separableClosure F E) E

/-- The finite inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E` as a natural number. It is defined to be zero
if such field extension is infinite. -/
/-
**Field.finInsepDegree** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：finInsepDegree : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / separableClosure F E` as a natural number. It is define
d to be zero
if such field extension is infinite.
-/
def finInsepDegree : ℕ := finrank (separableClosure F E) E
/-
**Field.finInsepDegree_def'** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finInsepDegree_def' : finInsepDegree F E = Cardinal.toNat (insepDegree F E
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finInsepDegree_def' : finInsepDegree F E = Cardinal.toNat (insepDegree F E) := rfl
/-
**Field.instNeZeroSepDegree** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：instNeZeroSepDegree : NeZero (sepDegree F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `rank_pos`：rank_pos [Nontrivial M] : 0 < Module.rank R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨rank_pos.ne'⟩
/-
**Field.instNeZeroInsepDegree** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：instNeZeroInsepDegree : NeZero (insepDegree F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `rank_pos`：rank_pos [Nontrivial M] : 0 < Module.rank R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance instNeZeroInsepDegree : NeZero (insepDegree F E) := ⟨rank_pos.ne'⟩
/-
**Field.instNeZeroFinInsepDegree** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
形式化陈述：instNeZeroFinInsepDegree [FiniteDimensional F E] : NeZero (finInsepDegree 
F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
instance instNeZeroFinInsepDegree [FiniteDimensional F E] :
    NeZero (finInsepDegree F E) := ⟨finrank_pos.ne'⟩

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same
separable degree over `F`. -/
/-
**Field.lift_sepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) : Cardinal.lift.{w} (sepDegree 
F E) = Cardinal.lift.{v} (sepDegree F K)
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then they have the same
separable degree over `F`.
-/
theorem lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) :=
  i.separableClosure.toLinearEquiv.lift_rank_eq

/-- The same-universe version of `Field.lift_sepDegree_eq_of_equiv`. -/
/-
**Field.sepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：sepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K)
 : sepDegree F E = sepDegree F K
参数：K : Type v；i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁

--- 原说明 ---
The same-universe version of `Field.lift_sepDegree_eq_of_equiv`.
-/
theorem sepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    sepDegree F E = sepDegree F K :=
  i.separableClosure.toLinearEquiv.rank_eq

/-- The separable degree multiplied by the inseparable degree is equal
to the (infinite) field extension degree. -/
/-
**Field.sepDegree_mul_insepDegree** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank 
F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
The separable degree multiplied by the inseparable degree is equal
to the (infinite) field extension degree.
-/
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E
/-
**Field.sepDegree_le_rank** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：sepDegree_le_rank : sepDegree F E <= Module.rank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.rank_bot_le_rank_of_isScalarTower`：Module.rank_bot_le_rank_of_isS
calarTower (T : Type u') [Module R R'] [NonAssocSemiring T] [Module R T] [Module
 R' T] [IsScalarTower R' T T] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.instFaithfulSMulSubtypeMem`：∀ {K : Type u_1} {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {X : Type u_4} 
  [inst_3 : SMul L X] [FaithfulSMu…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem sepDegree_le_rank : sepDegree F E ≤ Module.rank F E :=
  Module.rank_bot_le_rank_of_isScalarTower _ _ _
/-
**Field.insepDegree_le_rank** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：insepDegree_le_rank : insepDegree F E <= Module.rank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.rank_top_le_rank_of_isScalarTower`：Module.rank_top_le_rank_of_isS
calarTower [Module R' M] [SMulWithZero R R'] [IsScalarTower R R' M] [FaithfulSMu
l R R'] [IsScalarTower R R' R'…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem insepDegree_le_rank : insepDegree F E ≤ Module.rank F E :=
  Module.rank_top_le_rank_of_isScalarTower _ _ _

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same
inseparable degree over `F`. -/
/-
**Field.lift_insepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：lift_insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) : Cardinal.lift.{w} (insepDeg
ree F E) = Cardinal.lift.{v} (insepDegree F K)
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R 
≃+* R') (j : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.c
omp (algebraMap R S)) : l…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then they have the same
inseparable degree over `F`.
-/
theorem lift_insepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree F K) :=
  Algebra.lift_rank_eq_of_equiv_equiv i.separableClosure i rfl

/-- The same-universe version of `Field.lift_insepDegree_eq_of_equiv`. -/
/-
**Field.insepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：insepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] 
K) : insepDegree F E = insepDegree F K
参数：K : Type v；i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.rank_eq_of_equiv_equiv`：rank_eq_of_equiv_equiv (i : R ≃+* R') (j
 : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algeb
raMap R S)) : Module…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
The same-universe version of `Field.lift_insepDegree_eq_of_equiv`.
-/
theorem insepDegree_eq_of_equiv (K : Type v) [Field K] [Algebra F K] (i : E ≃ₐ[F] K) :
    insepDegree F E = insepDegree F K :=
  Algebra.rank_eq_of_equiv_equiv i.separableClosure i rfl

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same finite
inseparable degree over `F`. -/
/-
**Field.finInsepDegree_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) : finInsepDegree F E = finInsep
Degree F K
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Field.lift_insepDegree_eq_of_equiv`：lift_insepDegree_eq_of_equiv (i : E 
≃ₐ[F] K) : Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree 
F K)

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then they have the same finite
inseparable degree over `F`.
-/
theorem finInsepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finInsepDegree F E = finInsepDegree F K := by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat
    (lift_insepDegree_eq_of_equiv F E K i)

@[simp]
/-
**Field.sepDegree_self** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：sepDegree_self : sepDegree F F = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.sepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [inst
_1 : Field E] [inst_2 : Algebra F E],   Field.sepDegree F E = Module.rank F ↥(se
parableClo…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IntermediateField.rank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank F ↥⊥ = 1
-/
theorem sepDegree_self : sepDegree F F = 1 := by
  rw [sepDegree, Subsingleton.elim (separableClosure F F) ⊥, IntermediateField.rank_bot]

@[simp]
/-
**Field.insepDegree_self** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：insepDegree_self : insepDegree F F = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.insepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [in
st_1 : Field E] [inst_2 : Algebra F E],   Field.insepDegree F E = Module.rank (↥
(separableCl…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IntermediateField.rank_top`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank (↥⊤) E = 1
-/
theorem insepDegree_self : insepDegree F F = 1 := by
  rw [insepDegree, Subsingleton.elim (separableClosure F F) ⊤, IntermediateField.rank_top]

@[simp]
/-
**Field.finInsepDegree_self** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：finInsepDegree_self : finInsepDegree F F = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.finInsepDegree_def'`：finInsepDegree_def' : finInsepDegree F E = Ca
rdinal.toNat (insepDegree F E)
· 使用定理 `Field.insepDegree_self`：insepDegree_self : insepDegree F F = 1
· 使用定理 `Cardinal.one_toNat`：one_toNat : toNat 1 = 1
-/
theorem finInsepDegree_self : finInsepDegree F F = 1 := by
  rw [finInsepDegree_def', insepDegree_self, Cardinal.one_toNat]

end Field

namespace IntermediateField

/-- In a finitely generated field extension, there exists a maximal
separably generated field extension. -/
/-
**IntermediateField.exists_finset_maximalFor_isTranscendenceBasis_separableClosu
re** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
形式化陈述：exists_finset_maximalFor_isTranscendenceBasis_separableClosure [Algebra.Es
sFiniteType F E] : exists s : Finset E, MaximalFor (fun t : Set E => IsTranscend
enceBasis F ((↑) : t -> E)) (fun t => (separableClosure (adjoin F t) E).restrict
Scalars F) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IntermediateField.fg_top`：fg_top [Algebra.EssFiniteType F E] : (⊤ : Inte
rmediateField F E).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.isAlgebraic_adjoin_iff_top`：isAlgebraic_adjoin_iff_top
 : Algebra.IsAlgebraic (adjoin F s) S ↔ Algebra.IsAlgebraic (Algebra.adjoin F s)
 S
· 使用定理 `Algebra.isAlgebraic_iff_isIntegral`：∀ {K : Type u} {A : Type v} [inst : 
Field K] [inst_1 : Ring A] [inst_2 : Algebra K A],   Algebra.IsAlgebraic K A ↔ A
lgebra.IsIntegral K A
· 使用引理 `Algebra.isIntegral_of_surjective`：Algebra.isIntegral_of_surjective (H : 
Function.Surjective (algebraMap R B)) : Algebra.IsIntegral R B
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `exists_isTranscendenceBasis_subset`：exists_isTranscendenceBasis_subset [
NoZeroDivisors A] [FaithfulSMul R A] (s : Set A) [Algebra.IsAlgebraic (adjoin R 
s) A] : exists t, t subs…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `not_lt_iff_le_imp_ge`：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTranscendenceBasis.cardinalMk_eq`：∀ {ι : Type u} {R : Type u_1} {A : T
ype w} {x : ι → A} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R
 A]   [Nontrivial R] [No…
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Algebra.finite_of_essFiniteType_of_isAlgebraic`：∀ {F : Type u_1} [inst :
 Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] [Algebra.EssF
initeType F E]   [Algebra.IsAlgebrai…
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
In a finitely generated field extension, there exists a maximal
separably generated field extension.
-/
lemma exists_finset_maximalFor_isTranscendenceBasis_separableClosure
    [Algebra.EssFiniteType F E] :
    ∃ s : Finset E, MaximalFor (fun t : Set E ↦ IsTranscendenceBasis F ((↑) : t → E))
      (fun t ↦ (separableClosure (adjoin F t) E).restrictScalars F) s := by
  let d (s : Finset E) := Field.finInsepDegree (adjoin F (s : Set E)) E
  have Hexists : {s : Finset E | IsTranscendenceBasis F ((↑) : s → E)}.Nonempty := by
    have ⟨s, hs⟩ := IntermediateField.fg_top F E
    have : Algebra.IsAlgebraic (Algebra.adjoin F (s : Set E)) E := by
      rw [← isAlgebraic_adjoin_iff_top, hs, Algebra.isAlgebraic_iff_isIntegral]
      refine Algebra.isIntegral_of_surjective topEquiv.surjective
    have ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := F) (s : Set E)
    lift t to Finset E using s.finite_toSet.subset hts
    exact ⟨t, ht⟩
  let s := d.argminOn _ Hexists
  have hs := d.argminOn_mem _ Hexists
  refine ⟨s, hs, fun t ht ↦ not_lt_iff_le_imp_ge.mp fun H ↦ ?_⟩
  have : t.Finite := by
    simp [Set.Finite, ← Cardinal.mk_lt_aleph0_iff, ht.cardinalMk_eq hs, Cardinal.natCast_lt_aleph0]
  lift t to Finset E using this
  have : Module.Finite (adjoin F (s : Set E)) E := by
    apply +allowSynthFailures Algebra.finite_of_essFiniteType_of_isAlgebraic
    · exact .of_comp F _ _
    · convert! hs.isAlgebraic_field <;> simp [s]
  have : Module.Finite ((separableClosure (adjoin F (s : Set E)) E).restrictScalars F) E :=
    inferInstanceAs <| Module.Finite (separableClosure (adjoin F (s : Set E)) E) E
  exact d.not_lt_argminOn _ ht (by apply finrank_lt_of_gt H)

@[simp]
/-
**IntermediateField.sepDegree_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.lift_sepDegree_eq_of_equiv`：lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F
] K) : Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Field.sepDegree_self`：sepDegree_self : sepDegree F F = 1
-/
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
/-
**IntermediateField.insepDegree_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.lift_insepDegree_eq_of_equiv`：lift_insepDegree_eq_of_equiv (i : E 
≃ₐ[F] K) : Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree 
F K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Field.insepDegree_self`：insepDegree_self : insepDegree F F = 1
-/
theorem insepDegree_bot : insepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := lift_insepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [insepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{v, u}, Cardinal.lift_inj] at this

@[simp]
/-
**IntermediateField.finInsepDegree_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.finInsepDegree_eq_of_equiv`：finInsepDegree_eq_of_equiv (i : E ≃ₐ[F
] K) : finInsepDegree F E = finInsepDegree F K
· 使用定理 `Field.finInsepDegree_self`：finInsepDegree_self : finInsepDegree F F = 1
-/
theorem finInsepDegree_bot : finInsepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finInsepDegree_eq_of_equiv _ _ _ (botEquiv F E), finInsepDegree_self]

section Tower

variable [Algebra E K] [IsScalarTower F E K]

/-
**IntermediateField.lift_sepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateFiel
d E K)) = Cardinal.lift.{w} (sepDegree F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.lift_sepDegree_eq_of_equiv`：lift_sepDegree_eq_of_equiv (i : E ≃ₐ[F
] K) : Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lift_sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  lift_sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)
/-
**IntermediateField.lift_insepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : Intermediate
Field E K)) = Cardinal.lift.{w} (insepDegree F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.lift_insepDegree_eq_of_equiv`：lift_insepDegree_eq_of_equiv (i : E 
≃ₐ[F] K) : Cardinal.lift.{w} (insepDegree F E) = Cardinal.lift.{v} (insepDegree 
F K)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lift_insepDegree_bot' : Cardinal.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (insepDegree F E) :=
  lift_insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable {F}

@[simp]
/-
**IntermediateField.finInsepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：finInsepDegree_bot' : finInsepDegree F (⊥ : IntermediateField E K) = finIn
sepDegree F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IntermediateField.lift_insepDegree_bot'`：lift_insepDegree_bot' : Cardina
l.lift.{v} (insepDegree F (⊥ : IntermediateField E K)) = Cardinal.lift.{w} (inse
pDegree F E)
-/
theorem finInsepDegree_bot' :
    finInsepDegree F (⊥ : IntermediateField E K) = finInsepDegree F E := by
  simpa only [Cardinal.toNat_lift] using! congr_arg Cardinal.toNat (lift_insepDegree_bot' F E K)

@[simp]
/-
**IntermediateField.sepDegree_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.sepDegree_eq_of_equiv`：sepDegree_eq_of_equiv (K : Type v) [Field K
] [Algebra F K] (i : E ≃ₐ[F] K) : sepDegree F E = sepDegree F K
-/
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K :=
  sepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
/-
**IntermediateField.insepDegree_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree 
F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.insepDegree_eq_of_equiv`：insepDegree_eq_of_equiv (K : Type v) [Fie
ld K] [Algebra F K] (i : E ≃ₐ[F] K) : insepDegree F E = insepDegree F K
-/
theorem insepDegree_top : insepDegree F (⊤ : IntermediateField E K) = insepDegree F K :=
  insepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
/-
**IntermediateField.finInsepDegree_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finIns
epDegree F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.finInsepDegree_def'`：finInsepDegree_def' : finInsepDegree F E = Ca
rdinal.toNat (insepDegree F E)
· 使用定理 `IntermediateField.insepDegree_top`：insepDegree_top : insepDegree F (⊤ : 
IntermediateField E K) = insepDegree F K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem finInsepDegree_top : finInsepDegree F (⊤ : IntermediateField E K) = finInsepDegree F K := by
  rw [finInsepDegree_def', insepDegree_top, ← finInsepDegree_def']

variable (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

@[simp]
/-
**IntermediateField.sepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.sepDegree_eq_of_equiv`：sepDegree_eq_of_equiv (K : Type v) [Field K
] [Algebra F K] (i : E ≃ₐ[F] K) : sepDegree F E = sepDegree F K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem sepDegree_bot' : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
/-
**IntermediateField.insepDegree_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree
 F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.insepDegree_eq_of_equiv`：insepDegree_eq_of_equiv (K : Type v) [Fie
ld K] [Algebra F K] (i : E ≃ₐ[F] K) : insepDegree F E = insepDegree F K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem insepDegree_bot' : insepDegree F (⊥ : IntermediateField E K) = insepDegree F E :=
  insepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

variable (F) in
/-
**IntermediateField._root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower
** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Field.insepDegree_top_le_insepDegree_of_isScalarTower :
    insepDegree E K ≤ insepDegree F K := by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.rank_top_le_rank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
/-
**IntermediateField._root_.Field.insepDegree_le_of_left_le** 是 Mathlib 中的一个引理，位于
命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Field.insepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ ≤ E₂) :
    insepDegree E₂ K ≤ insepDegree E₁ K := by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact insepDegree_top_le_insepDegree_of_isScalarTower _ _ _

variable (F) in
/-
**IntermediateField._root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScala
rTower** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower [Module.Finite F K] :
    finInsepDegree E K ≤ finInsepDegree F K := by
  let := (IntermediateField.inclusion (separableClosure.le_restrictScalars F E K)).toAlgebra
  have : IsScalarTower (separableClosure F K) ((separableClosure E K).restrictScalars F) K :=
    .of_algebraMap_eq' rfl
  exact Module.finrank_top_le_finrank_of_isScalarTower
    (separableClosure F K) ((separableClosure E K).restrictScalars F) K

variable {K} in
/-
**IntermediateField.finInsepDegree_le_of_left_le** 是 Mathlib 中的一个引理，位于命名空间 `Inte
rmediateField`。
形式化陈述：finInsepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ <= E₂
) [Module.Finite E₁ K] : finInsepDegree E₂ K <= finInsepDegree E₁ K
参数：H : E₁ <= E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Field.finInsepDegree_top_le_finInsepDegree_of_isScalarTower`：∀ (F : Type
 u) (E : Type v) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K :
 Type v) [inst_3 : Field K]   [inst_4 : Algebra F…
-/
lemma finInsepDegree_le_of_left_le {E₁ E₂ : IntermediateField F K} (H : E₁ ≤ E₂)
    [Module.Finite E₁ K] : finInsepDegree E₂ K ≤ finInsepDegree E₁ K := by
  let := (IntermediateField.inclusion H).toAlgebra
  have : IsScalarTower E₁ E₂ K := .of_algebraMap_eq' rfl
  exact finInsepDegree_top_le_finInsepDegree_of_isScalarTower _ _ _

end Tower

end IntermediateField

/-- A separable extension has separable degree equal to degree. -/
/-
**Algebra.IsSeparable.sepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.sepDegree_eq [Algebra.IsSeparable F E] : sepDegree F E
 = Module.rank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.sepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [inst
_1 : Field E] [inst_2 : Algebra F E],   Field.sepDegree F E = Module.rank F ↥(se
parableClo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用定理 `IntermediateField.rank_top'`：∀ {F : Type u_1} [inst : Field F] {E : Type
 u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.rank F ↥⊤ = Module.ran
k F E

--- 原说明 ---
A separable extension has separable degree equal to degree.
-/
theorem Algebra.IsSeparable.sepDegree_eq [Algebra.IsSeparable F E] :
    sepDegree F E = Module.rank F E := by
  rw [sepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top']

/-- A separable extension has inseparable degree one. -/
/-
**Algebra.IsSeparable.insepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.insepDegree_eq [Algebra.IsSeparable F E] : insepDegree
 F E = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.insepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [in
st_1 : Field E] [inst_2 : Algebra F E],   Field.insepDegree F E = Module.rank (↥
(separableCl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `separableClosure.eq_top_iff`：separableClosure.eq_top_iff : separableClos
ure F E = ⊤ ↔ Algebra.IsSeparable F E
· 使用定理 `IntermediateField.rank_top`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank (↥⊤) E = 1

--- 原说明 ---
A separable extension has inseparable degree one.
-/
theorem Algebra.IsSeparable.insepDegree_eq [Algebra.IsSeparable F E] : insepDegree F E = 1 := by
  rw [insepDegree, (separableClosure.eq_top_iff F E).2 ‹_›, IntermediateField.rank_top]

/-- A separable extension has finite inseparable degree one. -/
/-
**Algebra.IsSeparable.finInsepDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsSeparable.finInsepDegree_eq [Algebra.IsSeparable F E] : finInsep
Degree F E = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsSeparable.insepDegree_eq`：Algebra.IsSeparable.insepDegree_eq [
Algebra.IsSeparable F E] : insepDegree F E = 1
· 使用定理 `Cardinal.one_toNat`：one_toNat : toNat 1 = 1

--- 原说明 ---
A separable extension has finite inseparable degree one.
-/
theorem Algebra.IsSeparable.finInsepDegree_eq [Algebra.IsSeparable F E] : finInsepDegree F E = 1 :=
  Cardinal.one_toNat ▸ congr(Cardinal.toNat $(insepDegree_eq F E))
