/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.PerfectPairing.Restrict
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Base change for root pairings

When the coefficients are a field, root pairings behave well with respect to restriction and
extension of scalars.

## Main results:
* `RootPairing.restrict`: if `RootPairing.pairing` takes values in a subfield, we may restrict to
  get a root _system_ with coefficients in the subfield. Of particular interest is the case when
  the pairing takes values in its prime subfield (which happens for crystallographic pairings).

## TODO

* Extension of scalars
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

-/

@[expose] public section

noncomputable section

open Set Function
open Submodule (span injective_subtype span subset_span span_setOfPred_mem_eq_top)

namespace RootPairing

/-- We say a root pairing is balanced if the root span and coroot span are perfectly
complementary.

All root systems are balanced and all finite root pairings over a field are balanced. -/
/-
**RootPairing.IsBalanced** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : AddCommGroup M] →           [inst_1 : AddCommGroup N] →   
          [inst_2 : CommRing R] →               [inst_3 : _root_.Module R M] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a root pairing is balanced if the root span and coroot span are perfectly
complementary.

All root systems are balanced and all finite root pairings over a field are bala
nced.
-/
class IsBalanced {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) : Prop where
  isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem] :
    P.IsBalanced where
  isPerfectCompl := by simp

variable {ι L M N : Type*}
  [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N)

section restrictScalars

variable (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section SubfieldValued

variable [P.IsValuedIn K]

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of scalars for a root pairing taking values in a subfield.

See also `RootPairing.restrictScalars`. -/
/-
**RootPairing.restrictScalars'** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：restrictScalars' : RootPairing ι K (span K (range P.root)) (span K (range 
P.coroot)) where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of scalars for a root pairing taking values in a subfield.

See also `RootPairing.restrictScalars`.
-/
def restrictScalars' :
    RootPairing ι K (span K (range P.root)) (span K (range P.coroot)) where
  toLinearMap := .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y ↦
      P.toLinearMap_apply_apply_mem_range_algebraMap K x x.property y y.property
  isPerfPair_toLinearMap := .restrictScalars_of_field P.toLinearMap _ _
    (injective_subtype _) (injective_subtype _) (by simpa using IsBalanced.isPerfectCompl) _
  root := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  coroot := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  root_coroot_two i := by
    have : algebraMap K L 2 = 2 := by
      rw [← Int.cast_two (R := K), ← Int.cast_two (R := L), map_intCast]
    exact FaithfulSMul.algebraMap_injective K L <| by simp [this]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_root i j
  reflectionPerm_coroot i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_coroot i j

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.restrictScalars' K).IsRootSystem where
  span_root_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']
  span_coroot_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']

set_option backward.isDefEq.respectTransparency.types false in
/-
**RootPairing.restrictScalars_toLinearMap_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 
`RootPairing`。
形式化陈述：∀ {ι : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d L] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : _root_.Modu
le L M] [inst_4 : _root_.Module L N] (P : RootPairing ι L M N)   (K : Type u_5) 
[inst_5 : Field K] [inst_6 : Algebra K L] [inst_7 : _root_.Module K M] [inst_8 :
 _root_.Module K N]   [inst_9 : IsScalarTower K L M] [inst_10 : IsScalarTower K 
L N] [inst_11 : P.IsBalanced] [inst_12 : P.IsValuedIn K]   (x : ↥(Submodule.span
 K (Set.range ⇑P.root))) (y : ↥(Submodule.span K (Set.range ⇑P.coroot))),   (alg
ebraMap K L) (((P.restrictScalars' K).toLinearMap x) y) = (P.toLinearMap ↑x) ↑y
参数：P : RootPairing ι L M N；K : Type u_5；x : ↥(Submodule.span K (Set.range ⇑P.roo
t))；y : ↥(Submodule.span K (Set.range ⇑P.coroot))；algebraMap K L；((P.restrictSca
lars' K).toLinearMap x) y；P.toLinearMap ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.restrictScalarsField_apply_apply`：∀ {K : Type u_1} {L : Type u
_2} {M : Type u_3} {N : Type u_4} [inst : Field K] [inst_1 : Field L] [inst_2 : 
Algebra K L]   [inst_3 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma restrictScalars_toLinearMap_apply_apply
    (x : span K (range P.root)) (y : span K (range P.coroot)) :
    algebraMap K L ((P.restrictScalars' K).toLinearMap x y) = P.toLinearMap x y := by
  simp [restrictScalars']
/-
**RootPairing.restrictScalars_coe_root** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d L] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : _root_.Modu
le L M] [inst_4 : _root_.Module L N] (P : RootPairing ι L M N)   (K : Type u_5) 
[inst_5 : Field K] [inst_6 : Algebra K L] [inst_7 : _root_.Module K M] [inst_8 :
 _root_.Module K N]   [inst_9 : IsScalarTower K L M] [inst_10 : IsScalarTower K 
L N] [inst_11 : P.IsBalanced] [inst_12 : P.IsValuedIn K]   (i : ι), ↑((P.restric
tScalars' K).root i) = P.root i
参数：P : RootPairing ι L M N；K : Type u_5；i : ι；(P.restrictScalars' K).root i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalars_coe_root (i : ι) :
    (P.restrictScalars' K).root i = P.root i :=
  rfl
/-
**RootPairing.restrictScalars_coe_coroot** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
形式化陈述：∀ {ι : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d L] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : _root_.Modu
le L M] [inst_4 : _root_.Module L N] (P : RootPairing ι L M N)   (K : Type u_5) 
[inst_5 : Field K] [inst_6 : Algebra K L] [inst_7 : _root_.Module K M] [inst_8 :
 _root_.Module K N]   [inst_9 : IsScalarTower K L M] [inst_10 : IsScalarTower K 
L N] [inst_11 : P.IsBalanced] [inst_12 : P.IsValuedIn K]   (i : ι), ↑((P.restric
tScalars' K).coroot i) = P.coroot i
参数：P : RootPairing ι L M N；K : Type u_5；i : ι；(P.restrictScalars' K).coroot i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalars_coe_coroot (i : ι) :
    (P.restrictScalars' K).coroot i = P.coroot i :=
  rfl
/-
**RootPairing.restrictScalars_pairing** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d L] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : _root_.Modu
le L M] [inst_4 : _root_.Module L N] (P : RootPairing ι L M N)   (K : Type u_5) 
[inst_5 : Field K] [inst_6 : Algebra K L] [inst_7 : _root_.Module K M] [inst_8 :
 _root_.Module K N]   [inst_9 : IsScalarTower K L M] [inst_10 : IsScalarTower K 
L N] [inst_11 : P.IsBalanced] [inst_12 : P.IsValuedIn K]   (i j : ι), (algebraMa
p K L) ((P.restrictScalars' K).pairing i j) = P.pairing i j
参数：P : RootPairing ι L M N；K : Type u_5；i j : ι；algebraMap K L；(P.restrictScalar
s' K).pairing i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.restrictScalars_toLinearMap_apply_apply`：∀ {ι : Type u_1} {L
 : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Field L] [inst_1 : AddCommGro
up M]   [inst_2 : AddCommGroup N] [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma restrictScalars_pairing (i j : ι) :
    algebraMap K L ((P.restrictScalars' K).pairing i j) = P.pairing i j := by
  simp only [pairing, restrictScalars_toLinearMap_apply_apply, restrictScalars_coe_root,
    restrictScalars_coe_coroot]

end SubfieldValued

/-- Restriction of scalars for a crystallographic root pairing. -/
/-
**RootPairing.restrictScalars** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：restrictScalars [P.IsCrystallographic] : RootPairing ι K (span K (range P.
root)) (span K (range P.coroot))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of scalars for a crystallographic root pairing.
-/
abbrev restrictScalars [P.IsCrystallographic] :
    RootPairing ι K (span K (range P.root)) (span K (range P.coroot)) :=
  have := IsValuedIn.trans P K ℤ
  P.restrictScalars' K

/-- Restriction of scalars to `ℚ` for a crystallographic root pairing in characteristic zero. -/
/-
**RootPairing.restrictScalarsRat** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：restrictScalarsRat [CharZero L] [P.IsCrystallographic]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of scalars to `ℚ` for a crystallographic root pairing in characteris
tic zero.
-/
abbrev restrictScalarsRat [CharZero L] [P.IsCrystallographic] :=
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ L)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ L)
  P.restrictScalars ℚ

end restrictScalars

end RootPairing

