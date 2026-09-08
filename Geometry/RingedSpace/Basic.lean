/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRingCat`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance <https://stacks.math.columbia.edu/tag/01HZ>.

-/

@[expose] public section

universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

open TopCat

open TopCat.Presheaf

namespace AlgebraicGeometry

-- The universes appear together in the type, but separately in the value.
set_option linter.checkUnivs false in
/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRingCat`. -/
/-
**AlgebraicGeometry.RingedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：RingedSpace : Type max (u + 1) (v + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRingCat`.
-/
abbrev RingedSpace : Type max (u + 1) (v + 1) :=
  SheafedSpace.{v + 1, v, u} CommRingCat.{v}

namespace RingedSpace

open SheafedSpace

@[simp]
/-
**AlgebraicGeometry.RingedSpace.res_zero** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.RingedSpace`。
形式化陈述：res_zero {X : RingedSpace.{u}} {U V : TopologicalSpace.Opens X} (hUV : U <
= V) : (0 : X.presheaf.obj (op V)) |_ U = (0 : X.presheaf.obj (op U))
参数：hUV : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma res_zero {X : RingedSpace.{u}} {U V : TopologicalSpace.Opens X}
    (hUV : U ≤ V) : (0 : X.presheaf.obj (op V)) |_ U = (0 : X.presheaf.obj (op U)) :=
  map_zero _

variable (X : RingedSpace)
/-
**AlgebraicGeometry.RingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Ri
ngedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort RingedSpace Type* where
  coe X := X.carrier

/-- If the germ of a section `f` is zero in the stalk at `x`, then `f` is zero on some neighbourhood
around `x`. -/
/-
**AlgebraicGeometry.RingedSpace.exists_res_eq_zero_of_germ_eq_zero** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.RingedSpace`。
形式化陈述：exists_res_eq_zero_of_germ_eq_zero (U : Opens X) (f : X.presheaf.obj (op U
)) (x : U) (h : X.presheaf.germ U x.val x.property f = 0) : exists (V : Opens X)
 (i : V ⟶ U) (_ : x.1 in V), X.presheaf.map i.op f = 0
参数：U : Opens X；f : X.presheaf.obj (op U)；x : U；h : X.presheaf.germ U x.val x.pro
perty f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …

--- 原说明 ---
If the germ of a section `f` is zero in the stalk at `x`, then `f` is zero on so
me neighbourhood
around `x`.
-/
lemma exists_res_eq_zero_of_germ_eq_zero (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
    (h : X.presheaf.germ U x.val x.property f = 0) :
    ∃ (V : Opens X) (i : V ⟶ U) (_ : x.1 ∈ V), X.presheaf.map i.op f = 0 := by
  have h1 : X.presheaf.germ U x.val x.property f = X.presheaf.germ U x.val x.property 0 := by simpa
  obtain ⟨V, hv, i, _, (hv4 : (X.presheaf.map i.op) f = (X.presheaf.map _) 0)⟩ :=
    TopCat.Presheaf.germ_eq X.presheaf x.1 x.2 x.2 f 0 h1
  use V, i, hv
  simpa using hv4

set_option backward.isDefEq.respectTransparency.types false in
/--
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
/-
**AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.RingedSpace`。
形式化陈述：isUnit_res_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : X
) (hx : x in U) (h : IsUnit (X.presheaf.germ U x hx f)) : exists (V : Opens X) (
i : V ⟶ U) (_ : x in V), IsUnit (X.presheaf.map i.op f)
参数：U : Opens X；f : X.presheaf.obj (op U)；x : X；hx : x in U；h : IsUnit (X.preshea
f.germ U x hx f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a u
nit on some small
neighborhood around `x`.
-/
theorem isUnit_res_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x ∈ U)
    (h : IsUnit (X.presheaf.germ U x hx f)) :
    ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V), IsUnit (X.presheaf.map i.op f) := by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.exists_germ_eq g'
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  replace heq : (X.presheaf.germ _ x hxW) ((X.presheaf.map (U.infLELeft V).op) f *
      (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ _ x hxW) 1 := by
    rwa [map_mul, map_one, X.presheaf.germ_res_apply (Opens.infLELeft U V) x hxW f,
      X.presheaf.germ_res_apply (Opens.infLERight U V) x hxW g]
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x hxW hxW _ _ heq
  use W', i₁ ≫ Opens.infLELeft U V, hxW'
  simp only [map_mul, map_one] at heq'
  simpa using .of_mul_eq_one _ heq'

set_option backward.isDefEq.respectTransparency false in
/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
/-
**AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.RingedSpace`。
形式化陈述：isUnit_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (h : foral
l (x) (hx : x in U), IsUnit (X.presheaf.germ U x hx f)) : IsUnit f
参数：U : Opens X；f : X.presheaf.obj (op U)；h : forall (x) (hx : x in U), IsUnit (X
.presheaf.germ U x hx f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `TopCat.Sheaf.existsUnique_gluing'`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 
: (X Y : C) → FunLike (…
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `TopCat.Sheaf.eq_of_locally_eq'`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 : (
X Y : C) → FunLike (…
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ`：isUnit_res_of_i
sUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) (h : 
IsUnit (X.presheaf.germ U x hx f)) : exists (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If a section `f` is a unit in each stalk, `f` must be a unit.
-/
theorem isUnit_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U))
    (h : ∀ (x) (hx : x ∈ U), IsUnit (X.presheaf.germ U x hx f)) : IsUnit f := by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x x.2 (h x.1 x.2)
  have hcover : U ≤ iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    tauto
  -- Let `g x` denote the inverse of `f` in `U x`.
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  have ic : IsCompatible (sheaf X).obj V g := by
    intro x y
    apply section_ext X.sheaf (V x ⊓ V y)
    rintro z ⟨hzVx, hzVy⟩
    rw [germ_res_apply, germ_res_apply]
    apply (h z ((iVU x).le hzVx)).mul_right_inj.mp
    rw [← germ_res_apply X.presheaf (iVU x) z hzVx f]
    -- Porting note: change was not necessary in Lean3
    change X.presheaf.germ _ z hzVx _ * (X.presheaf.germ _ z hzVx _) =
      X.presheaf.germ _ z hzVx _ * X.presheaf.germ _ z hzVy (g y)
    rw [← map_mul, hg x, germ_res_apply X.presheaf _ _ _ f,
      ← germ_res_apply X.presheaf (iVU y) z hzVy f, ← map_mul, (hg y), map_one, map_one]
  -- We claim that these local inverses glue together to a global inverse of `f`.
  obtain ⟨gl, gl_spec, -⟩ :
    -- We need to rephrase the result from `ConcreteCategory` to `CommRingCat`.
    ∃ gl : X.presheaf.obj (op U), (∀ i, ((sheaf X).obj.map (iVU i).op) gl = g i) ∧ _ :=
    X.sheaf.existsUnique_gluing' V U iVU hcover g ic
  refine .of_mul_eq_one gl <| X.sheaf.eq_of_locally_eq' V U iVU hcover _ _ fun i ↦ ?_
  -- We need to rephrase the goal from `ConcreteCategory` to `CommRingCat`.
  change ((sheaf X).obj.map (iVU i).op).hom (f * gl) = ((sheaf X).obj.map (iVU i).op) 1
  rw [map_one, map_mul, gl_spec]
  exact hg i

/-- The basic open of a section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
/-
**AlgebraicGeometry.RingedSpace.basicOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.RingedSpace`。
形式化陈述：basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : Opens X where carrie
r
参数：f : X.presheaf.obj (op U)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basic open of a section `f` is the set of all points `x`, such that the germ
 of `f` at
`x` is a unit.
-/
def basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : Opens X where
  carrier := { x : X | ∃ (hx : x ∈ U), IsUnit (X.presheaf.germ U x hx f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hxU hx
    use V.1
    refine ⟨?_, V.2, hxV⟩
    intro y hy
    use i.le hy
    convert! RingHom.isUnit_map (X.presheaf.germ _ y hy).hom hf
    exact (X.presheaf.germ_res_apply i y hy f).symm
/-
**AlgebraicGeometry.RingedSpace.mem_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.RingedSpace`。
形式化陈述：mem_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x in
 U) : x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f)
参数：f : X.presheaf.obj (op U)；x : X；hx : x in U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem mem_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x ∈ U) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  ⟨Exists.choose_spec, (⟨hx, ·⟩)⟩

/-- A variant of `mem_basicOpen` with bundled `x : U`. -/
@[simp]
/-
**AlgebraicGeometry.RingedSpace.mem_basicOpen'** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.RingedSpace`。
形式化陈述：mem_basicOpen' {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) : ↑x in X
.basicOpen f ↔ IsUnit (X.presheaf.germ U x.1 x.2 f)
参数：f : X.presheaf.obj (op U)；x : U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A variant of `mem_basicOpen` with bundled `x : U`.
-/
theorem mem_basicOpen' {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) :
    ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x.1 x.2 f) :=
  mem_basicOpen X f x.1 x.2

@[simp]
/-
**AlgebraicGeometry.RingedSpace.mem_top_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.RingedSpace`。
形式化陈述：mem_top_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) : x in X.basicOpen f
 ↔ IsUnit (X.presheaf.Γgerm x f)
参数：f : X.presheaf.obj (op ⊤)；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
-/
theorem mem_top_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.Γgerm x f) :=
  mem_basicOpen X f x .intro
/-
**AlgebraicGeometry.RingedSpace.basicOpen_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.RingedSpace`。
形式化陈述：basicOpen_le {U : Opens X} (f : X.presheaf.obj (op U)) : X.basicOpen f <= 
U
参数：f : X.presheaf.obj (op U)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basicOpen_le {U : Opens X} (f : X.presheaf.obj (op U)) : X.basicOpen f ≤ U := by
  rintro x ⟨h, _⟩; exact h

/-- The restriction of a section `f` to the basic open of `f` is a unit. -/
/-
**AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.RingedSpace`。
形式化陈述：isUnit_res_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : IsUnit (X
.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f)
参数：f : X.presheaf.obj (op U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ`：isUnit_of_isUnit_ge
rm (U : Opens X) (f : X.presheaf.obj (op U)) (h : forall (x) (hx : x in U), IsUn
it (X.presheaf.germ U x hx f)) : IsUnit f
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_le`：basicOpen_le {U : Opens X} (
f : X.presheaf.obj (op U)) : X.basicOpen f <= U
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …

--- 原说明 ---
The restriction of a section `f` to the basic open of `f` is a unit.
-/
theorem isUnit_res_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) := by
  apply isUnit_of_isUnit_germ
  rintro x ⟨hxU, hx⟩
  convert! hx
  exact X.presheaf.germ_res_apply _ _ _ _

@[simp]
/-
**AlgebraicGeometry.RingedSpace.basicOpen_res** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.RingedSpace`。
形式化陈述：basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) : @ba
sicOpen X (unop V) (X.presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f
参数：Opens X；i : U ⟶ V；f : X.presheaf.obj U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_res_apply'`：germ_res_apply' (F : X.Presheaf C) {U V
 : Opens X} (i : op V ⟶ op U) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) 
: F.germ U x hx (F.ma…
-/
theorem basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f := by
  ext x; constructor
  · rintro ⟨hxV, hx⟩
    rw [germ_res_apply' X.presheaf] at hx
    exact ⟨hxV, i.unop.le hxV, hx⟩
  · rintro ⟨hxV, _, hx⟩
    refine ⟨hxV, ?_⟩
    rw [germ_res_apply' X.presheaf]
    exact hx

/-- High priority: This should fire before `basicOpen_res`. -/
@[simp (high)]
/-
**AlgebraicGeometry.RingedSpace.basicOpen_res_eq** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.RingedSpace`。
形式化陈述：basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf
.obj U) : @basicOpen X (unop V) (X.presheaf.map i f) = @RingedSpace.basicOpen X 
(unop U) f
参数：Opens X；i : U ⟶ V；f : X.presheaf.obj U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_res`：basicOpen_res {U V : (Opens
 X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) : @basicOpen X (unop V) (X.presheaf.ma
p i f) = unop V ⊓ @basicOpen X (u…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `CommRingCat.id_apply`：id_apply (R : CommRingCat) (r : R) : (𝟙 R : R ⟶ R)
 r = r
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)

--- 原说明 ---
High priority: This should fire before `basicOpen_res`.
-/
theorem basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = @RingedSpace.basicOpen X (unop U) f := by
  apply le_antisymm
  · rw [X.basicOpen_res i f]; exact inf_le_right
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp, IsIso.hom_inv_id, X.presheaf.map_id,
        CommRingCat.id_apply] at this
    rw [this]
    exact inf_le_right

@[simp]
/-
**AlgebraicGeometry.RingedSpace.basicOpen_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.RingedSpace`。
形式化陈述：basicOpen_mul {U : Opens X} (f g : X.presheaf.obj (op U)) : X.basicOpen (f
 * g) = X.basicOpen f ⊓ X.basicOpen g
参数：f g : X.presheaf.obj (op U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_le`：basicOpen_le {U : Opens X} (
f : X.presheaf.obj (op U)) : X.basicOpen f <= U
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem basicOpen_mul {U : Opens X} (f g : X.presheaf.obj (op U)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g := by
  ext x
  by_cases hx : x ∈ U
  · simp [mem_basicOpen (hx := hx)]
  · simp [mt (basicOpen_le X _ ·) hx]

@[simp]
/-
**AlgebraicGeometry.RingedSpace.basicOpen_pow** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.RingedSpace`。
形式化陈述：basicOpen_pow {U : Opens X} (f : X.presheaf.obj (op U)) (n : Nat) (h : 0 <
 n) : X.basicOpen (f ^ n) = X.basicOpen f
参数：f : X.presheaf.obj (op U)；n : Nat；h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_mul`：basicOpen_mul {U : Opens X}
 (f g : X.presheaf.obj (op U)) : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOp
en g
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma basicOpen_pow {U : Opens X} (f : X.presheaf.obj (op U)) (n : ℕ) (h : 0 < n) :
    X.basicOpen (f ^ n) = X.basicOpen f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  induction k with
  | zero => simp
  | succ n hn => rw [pow_add]; simp_all
/-
**AlgebraicGeometry.RingedSpace.basicOpen_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.RingedSpace`。
形式化陈述：basicOpen_of_isUnit {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit
 f) : X.basicOpen f = U
参数：op U；hf : IsUnit f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_le`：basicOpen_le {U : Opens X} (
f : X.presheaf.obj (op U)) : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem basicOpen_of_isUnit {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f) :
    X.basicOpen f = U := by
  apply le_antisymm
  · exact X.basicOpen_le f
  intro x hx
  rw [X.mem_basicOpen f x hx]
  exact RingHom.isUnit_map _ hf

/--
The zero locus of a set of sections `s` over an open set `U` is the closed set consisting of
the complement of `U` and of all points of `U`, where all elements of `f` vanish.
-/
/-
**AlgebraicGeometry.RingedSpace.zeroLocus** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.RingedSpace`。
形式化陈述：zeroLocus {U : Opens X} (s : Set (X.presheaf.obj (op U))) : Set X
参数：s : Set (X.presheaf.obj (op U))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero locus of a set of sections `s` over an open set `U` is the closed set c
onsisting of
the complement of `U` and of all points of `U`, where all elements of `f` vanish
.
-/
def zeroLocus {U : Opens X} (s : Set (X.presheaf.obj (op U))) : Set X :=
  ⋂ f ∈ s, (X.basicOpen f)ᶜ
/-
**AlgebraicGeometry.RingedSpace.zeroLocus_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.RingedSpace`。
形式化陈述：zeroLocus_isClosed {U : Opens X} (s : Set (X.presheaf.obj (op U))) : IsClo
sed (X.zeroLocus s)
参数：s : Set (X.presheaf.obj (op U))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
lemma zeroLocus_isClosed {U : Opens X} (s : Set (X.presheaf.obj (op U))) :
    IsClosed (X.zeroLocus s) := by
  apply isClosed_biInter
  intro i _
  simp only [isClosed_compl_iff]
  exact Opens.isOpen (X.basicOpen i)
/-
**AlgebraicGeometry.RingedSpace.zeroLocus_singleton** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.RingedSpace`。
形式化陈述：zeroLocus_singleton {U : Opens X} (f : X.presheaf.obj (op U)) : X.zeroLocu
s {f} = (X.basicOpen f).carrierᶜ
参数：f : X.presheaf.obj (op U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_left`：iInter_iInter_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋂ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroLocus_singleton {U : Opens X} (f : X.presheaf.obj (op U)) :
    X.zeroLocus {f} = (X.basicOpen f).carrierᶜ := by
  simp [zeroLocus]

@[simp]
/-
**AlgebraicGeometry.RingedSpace.zeroLocus_empty_eq_univ** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.RingedSpace`。
形式化陈述：zeroLocus_empty_eq_univ {U : Opens X} : X.zeroLocus (∅ : Set (X.presheaf.o
bj (op U))) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroLocus_empty_eq_univ {U : Opens X} :
    X.zeroLocus (∅ : Set (X.presheaf.obj (op U))) = Set.univ := by
  simp [zeroLocus]

@[simp]
/-
**AlgebraicGeometry.RingedSpace.mem_zeroLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.RingedSpace`。
形式化陈述：mem_zeroLocus_iff {U : Opens X} (s : Set (X.presheaf.obj (op U))) (x : X) 
: x in X.zeroLocus s ↔ forall f in s, x ∉ X.basicOpen f
参数：s : Set (X.presheaf.obj (op U))；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_zeroLocus_iff {U : Opens X} (s : Set (X.presheaf.obj (op U))) (x : X) :
    x ∈ X.zeroLocus s ↔ ∀ f ∈ s, x ∉ X.basicOpen f := by
  simp [zeroLocus]

end RingedSpace

end AlgebraicGeometry

