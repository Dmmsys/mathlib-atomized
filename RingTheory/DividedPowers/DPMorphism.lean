/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic

/-! # Divided power morphisms

Let `A` and `B` be commutative (semi)rings, let `I` be an ideal of `A` and let `J` be an ideal of
`B`. Given divided power structures on `I` and `J`, a ring morphism `A →+* B` is a *divided
power morphism* if it is compatible with these divided power structures.

## Main definitions

* `DividedPowers.IsDPMorphism` : given divided power structures on the `A`-ideal `I` and the
  `B`-ideal `J`, a ring morphism `A →+* B` is a divided power morphism if it is compatible with
  these divided power structures.
* `DividedPowers.DPMorphism` : a bundled version of `IsDPMorphism`.
* `DividedPowers.ideal_from_ringHom` : given a ring homomorphism `A →+* B` and ideals `I ⊆ A` and
  `J ⊆ B` such that `I.map f ≤ J`, this is the `A`-ideal on which
  `f (hI.dpow n x) = hJ.dpow n (f x)`.
* `DividedPowers.DPMorphism.fromGens` : the `DPMorphism` induced by a ring morphism, given that
  divided powers are compatible on a generating set.

## Main results

* `DividedPowers.dpow_eq_from_gens` : if two divided power structures on an ideal `I` agree on a
  generating set, then they are equal.

## Implementation remarks

We provided both a bundled and an unbundled definition of divided power morphisms. For developing
the basic theory, the unbundled version `IsDPMorphism` is more convenient. However, we anticipate
that the bundled version `DPMorphism` will be better for the development of crystalline
cohomology.

## References

* [P. Berthelot, *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus, *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby, *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby, *Les algèbres à puissances dividées*][Roby-1965]
-/

@[expose] public section

open Ideal Set SetLike

namespace DividedPowers

/-- Given divided power structures on the `A`-ideal `I` and the `B`-ideal `J`, a ring morphism
  `A → B` is a divided power morphism if it is compatible with these divided power structures. -/
/-
**DividedPowers.IsDPMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 `DividedPowers`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     [inst : CommSemiring A] →       [i
nst_1 : CommSemiring B] → {I : Ideal A} → {J : Ideal B} → DividedPowers I → Divi
dedPowers J → (A →+* B) → Prop
参数：A →+* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given divided power structures on the `A`-ideal `I` and the `B`-ideal `J`, a rin
g morphism
  `A → B` is a divided power morphism if it is compatible with these divided pow
er structures.
-/
structure IsDPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop where
  ideal_comp : I.map f ≤ J
  dpow_comp : ∀ {n : ℕ}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)
/-
**DividedPowers.isDPMorphism_def** 是 Mathlib 中的一个引理，位于命名空间 `DividedPowers`。
形式化陈述：isDPMorphism_def (f : A ->+* B) : IsDPMorphism hI hJ f ↔ I.map f <= J ∧ fo
rall {n}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a)
参数：f : A ->+* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.IsDPMorphism.ideal_comp`：∀ {A : Type u_1} {B : Type u_2} [
inst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {
hI : DividedPowers I} {hJ :…
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…
-/
lemma isDPMorphism_def (f : A →+* B) :
    IsDPMorphism hI hJ f ↔ I.map f ≤ J ∧ ∀ {n}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  ⟨fun h ↦ ⟨h.ideal_comp, h.dpow_comp⟩, fun ⟨h1, h2⟩ ↦ IsDPMorphism.mk h1 h2⟩
/-
**DividedPowers.isDPMorphism_iff** 是 Mathlib 中的一个引理，位于命名空间 `DividedPowers`。
形式化陈述：isDPMorphism_iff (f : A ->+* B) : IsDPMorphism hI hJ f ↔ I.map f <= J ∧ fo
rall n != 0, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a)
参数：f : A ->+* B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DividedPowers.isDPMorphism_def`：isDPMorphism_def (f : A ->+* B) : IsDPMo
rphism hI hJ f ↔ I.map f <= J ∧ forall {n}, forall a in I, hJ.dpow n (f a) = f (
hI.dpow n a)
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `DividedPowers.dpow_zero`：∀ {A : Type u_1} [inst : CommSemiring A] {I : I
deal A} (self : DividedPowers I) {x : A}, x ∈ I → self.dpow 0 x = 1
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
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
-/
lemma isDPMorphism_iff (f : A →+* B) :
    IsDPMorphism hI hJ f ↔ I.map f ≤ J ∧ ∀ n ≠ 0, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) := by
  rw [isDPMorphism_def, and_congr_right_iff]
  refine fun hIJ ↦ ⟨fun H n _ ↦ H, fun H n ↦ ?_⟩
  by_cases hn : n = 0
  · intro _ ha
    rw [hn, hI.dpow_zero ha, hJ.dpow_zero (hIJ (mem_map_of_mem f ha)), map_one]
  · exact H n hn

namespace IsDPMorphism

variable {hI hJ} {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K)

/-
**DividedPowers.IsDPMorphism.map_dpow** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers.I
sDPMorphism`。
形式化陈述：map_dpow {f : A ->+* B} (hf : IsDPMorphism hI hJ f) {n : Nat} {a : A} (ha 
: a in I) : f (hI.dpow n a) = hJ.dpow n (f a)
参数：hf : IsDPMorphism hI hJ f；ha : a in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…
-/
theorem map_dpow {f : A →+* B} (hf : IsDPMorphism hI hJ f) {n : ℕ} {a : A} (ha : a ∈ I) :
    f (hI.dpow n a) = hJ.dpow n (f a) := (hf.2 a ha).symm
/-
**DividedPowers.IsDPMorphism.comp** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers.IsDPM
orphism`。
形式化陈述：comp {f : A ->+* B} {g : B ->+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPM
orphism hI hJ f) : IsDPMorphism hI hK (g.comp f)
参数：hg : IsDPMorphism hJ hK g；hf : IsDPMorphism hI hJ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `DividedPowers.IsDPMorphism.ideal_comp`：∀ {A : Type u_1} {B : Type u_2} [
inst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {
hI : DividedPowers I} {hJ :…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
-/
theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
    IsDPMorphism hI hK (g.comp f) := by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha ↦ ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha, hg.2]
  exact hf.1 (mem_map_of_mem f ha)

end IsDPMorphism

/-- A bundled divided power morphism between rings endowed with divided power structures. -/
@[ext]
/-
**DividedPowers.DPMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 `DividedPowers`。
形式化陈述：{A : Type u_3} →   {B : Type u_4} →     [inst : CommSemiring A] →       [i
nst_1 : CommSemiring B] → {I : Ideal A} → {J : Ideal B} → DividedPowers I → Divi
dedPowers J → Type (max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled divided power morphism between rings endowed with divided power struct
ures.
-/
structure DPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) extends RingHom A B where
  ideal_comp : I.map toRingHom ≤ J
  dpow_comp : ∀ {n : ℕ}, ∀ a ∈ I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)

namespace DPMorphism

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

/-
**DividedPowers.DPMorphism.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `DividedPowers.
DPMorphism`。
形式化陈述：instFunLike : FunLike (DPMorphism hI hJ) A B where coe h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (DPMorphism hI hJ) A B where
  coe h := h.toRingHom
  coe_injective h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh'; ext; rw [hh']
/-
**DividedPowers.DPMorphism.coe_ringHom** 是 Mathlib 中的一个实例，位于命名空间 `DividedPowers.
DPMorphism`。
形式化陈述：coe_ringHom : CoeOut (DPMorphism hI hJ) (A ->+* B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coe_ringHom : CoeOut (DPMorphism hI hJ) (A →+* B) := ⟨DPMorphism.toRingHom⟩
/-
**DividedPowers.DPMorphism.coe_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `DividedPower
s.DPMorphism`。
形式化陈述：∀ {A : Type u_3} {B : Type u_4} [inst : CommSemiring A] [inst_1 : CommSemi
ring B] {I : Ideal A} {J : Ideal B}   (hI : DividedPowers I) (hJ : DividedPowers
 J) {f : hI.DPMorphism hJ}, ⇑f.toRingHom = ⇑f
参数：hI : DividedPowers I；hJ : DividedPowers J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toRingHom {f : DPMorphism hI hJ} : ⇑(f : A →+* B) = f := rfl
/-
**DividedPowers.DPMorphism.toRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `DividedPow
ers.DPMorphism`。
形式化陈述：∀ {A : Type u_3} {B : Type u_4} [inst : CommSemiring A] [inst_1 : CommSemi
ring B] {I : Ideal A} {J : Ideal B}   (hI : DividedPowers I) (hJ : DividedPowers
 J) {f : hI.DPMorphism hJ} {a : A}, f.toRingHom a = f a
参数：hI : DividedPowers I；hJ : DividedPowers J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toRingHom_apply {f : DPMorphism hI hJ} {a : A} : f.toRingHom a = f a := rfl

variable {hI hJ}
/-
**DividedPowers.DPMorphism.isDPMorphism** 是 Mathlib 中的一个引理，位于命名空间 `DividedPowers
.DPMorphism`。
形式化陈述：isDPMorphism (f : DPMorphism hI hJ) : IsDPMorphism hI hJ f.toRingHom
参数：f : DPMorphism hI hJ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.DPMorphism.ideal_comp`：∀ {A : Type u_3} {B : Type u_4} [in
st : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {hI
 : DividedPowers I} {hJ :…
· 使用定理 `DividedPowers.DPMorphism.dpow_comp`：∀ {A : Type u_3} {B : Type u_4} [ins
t : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {hI 
: DividedPowers I} {hJ :…
-/
lemma isDPMorphism (f : DPMorphism hI hJ) : IsDPMorphism hI hJ f.toRingHom :=
  ⟨f.ideal_comp, f.dpow_comp⟩

/-- A constructor for `DPMorphism` from a ring homomorphism `f : A →+* B` satisfying
  `IsDPMorphism hI hJ f`. -/
/-
**DividedPowers.DPMorphism.mk'** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.DPMorphi
sm`。
形式化陈述：mk' {f : A ->+* B} (hf : IsDPMorphism hI hJ f) : DPMorphism hI hJ
参数：hf : IsDPMorphism hI hJ f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.IsDPMorphism.ideal_comp`：∀ {A : Type u_1} {B : Type u_2} [
inst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {
hI : DividedPowers I} {hJ :…
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…

--- 原说明 ---
A constructor for `DPMorphism` from a ring homomorphism `f : A →+* B` satisfying
  `IsDPMorphism hI hJ f`.
-/
def mk' {f : A →+* B} (hf : IsDPMorphism hI hJ f) : DPMorphism hI hJ :=
  ⟨f, hf.1, hf.2⟩

variable (hI hJ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given a ring homomorphism `A → B` and ideals `I ⊆ A` and `J ⊆ B` such that `I.map f ≤ J`,
  this is the `A`-ideal on which `f (hI.dpow n x) = hJ.dpow n (f x)`.
  See [N. Roby, *Les algèbres à puissances dividées* (Proposition 2)][Roby-1965]. -/
/-
**DividedPowers.DPMorphism._root_.DividedPowers.ideal_from_ringHom** 是 Mathlib 中
的一个定义，位于命名空间 `DividedPowers.DPMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring homomorphism `A → B` and ideals `I ⊆ A` and `J ⊆ B` such that `I.ma
p f ≤ J`,
  this is the `A`-ideal on which `f (hI.dpow n x) = hJ.dpow n (f x)`.
  See [N. Roby, *Les algèbres à puissances dividées* (Proposition 2)][Roby-1965]
.
-/
def _root_.DividedPowers.ideal_from_ringHom {f : A →+* B} (hf : I.map f ≤ J) : Ideal A where
  carrier  := {x ∈ I | ∀ n : ℕ, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := fun hx hy ↦ by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    refine ⟨I.add_mem hx.1 hy.1, fun n ↦ ?_⟩
    rw [hI.dpow_add hx.1 hy.1, map_sum,
      hJ.dpow_add (hf (mem_map_of_mem f hx.1)) (hf (mem_map_of_mem f hy.1))]
    apply congr_arg
    ext k
    rw [map_mul, hx.2, hy.2]
  zero_mem' := by
    simp only [mem_ofPred_eq, Submodule.zero_mem, map_zero, true_and]
    intro n
    induction n with
    | zero => rw [hI.dpow_zero I.zero_mem, hJ.dpow_zero J.zero_mem, map_one]
    | succ n => rw [hI.dpow_eval_zero n.succ_ne_zero, hJ.dpow_eval_zero n.succ_ne_zero, map_zero]
  smul_mem' := fun r x hx ↦ by
    refine ⟨I.smul_mem r hx.1, (fun n ↦ ?_)⟩
    rw [smul_eq_mul, hI.dpow_mul hx.1, map_mul, map_mul, map_pow,
      hJ.dpow_mul (hf (mem_map_of_mem f hx.1)), hx.2 n]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `DPMorphism` induced by a ring morphism, given that divided powers are compatible on a
  generating set.
  See [N. Roby, *Les algèbres à puissances dividées* (Proposition 3)][Roby-1965]. -/
/-
**DividedPowers.DPMorphism.fromGens** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.DPM
orphism`。
形式化陈述：fromGens {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <= J) 
(h : forall {n : Nat}, forall x in S, f (hI.dpow n x) = hJ.dpow n (f x)) : DPMor
phism hI hJ where toRingHom
参数：hS : I = span S；hf : I.map f <= J；h : forall {n : Nat}, forall x in S, f (hI.
dpow n x) = hJ.dpow n (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `DPMorphism` induced by a ring morphism, given that divided powers are compa
tible on a
  generating set.
  See [N. Roby, *Les algèbres à puissances dividées* (Proposition 3)][Roby-1965]
.
-/
def fromGens {f : A →+* B} {S : Set A} (hS : I = span S) (hf : I.map f ≤ J)
    (h : ∀ {n : ℕ}, ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) : DPMorphism hI hJ where
  toRingHom          := f
  ideal_comp         := hf
  dpow_comp {n} x hx := by
    have hS' : S ⊆ ideal_from_ringHom hI hJ hf := fun y hy ↦ by
      simp only [mem_coe, ideal_from_ringHom, Submodule.mem_mk]
      exact ⟨hS ▸ subset_span hy, fun n => h y hy⟩
    rw [← span_le, ← hS] at hS'
    exact ((hS' hx).2 n).symm

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The identity map as a `DPMorphism`. -/
/-
**DividedPowers.DPMorphism.id** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.DPMorphis
m`。
形式化陈述：id : DPMorphism hI hI where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as a `DPMorphism`.
-/
def id : DPMorphism hI hI where
  toRingHom     := RingHom.id A
  ideal_comp    := by simp only [map_id, le_refl]
  dpow_comp _ _ := by simp only [RingHom.id_apply]
/-
**DividedPowers.DPMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `DividedPowers.DPMorphism`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (DPMorphism hI hI) := ⟨DPMorphism.id hI⟩
/-
**DividedPowers.DPMorphism.fromGens_coe** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers
.DPMorphism`。
形式化陈述：fromGens_coe {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <=
 J) (h : forall {n : Nat}, forall x in S, f (hI.dpow n x) = hJ.dpow n (f x)) : (
fromGens hI hJ hS hf h).toRingHom = f
参数：hS : I = span S；hf : I.map f <= J；h : forall {n : Nat}, forall x in S, f (hI.
dpow n x) = hJ.dpow n (f x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromGens_coe {f : A →+* B} {S : Set A} (hS : I = span S) (hf : I.map f ≤ J)
    (h : ∀ {n : ℕ}, ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    (fromGens hI hJ hS hf h).toRingHom = f := rfl

end DPMorphism

namespace IsDPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)

open DPMorphism

/-
**DividedPowers.IsDPMorphism.on_span** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers.Is
DPMorphism`。
形式化陈述：on_span {f : A ->+* B} {S : Set A} (hS : I = span S) (hS' : forall s in S,
 f s in J) (hdp : forall {n : Nat}, forall a in S, f (hI.dpow n a) = hJ.dpow n (
f a)) : IsDPMorphism hI hJ f
参数：hS : I = span S；hS' : forall s in S, f s in J；hdp : forall {n : Nat}, forall 
a in S, f (hI.dpow n a) = hJ.dpow n (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DividedPowers.DPMorphism.fromGens_coe`：fromGens_coe {f : A ->+* B} {S : 
Set A} (hS : I = span S) (hf : I.map f <= J) (h : forall {n : Nat}, forall x in 
S, f (hI.dpow n x) = hJ.dpo…
· 使用定理 `DividedPowers.DPMorphism.dpow_comp`：∀ {A : Type u_3} {B : Type u_4} [ins
t : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {hI 
: DividedPowers I} {hJ :…
-/
theorem on_span {f : A →+* B} {S : Set A} (hS : I = span S) (hS' : ∀ s ∈ S, f s ∈ J)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) : IsDPMorphism hI hJ f := by
  suffices h : I.map f ≤ J by
    exact ⟨h, fun a ha ↦ by
      rw [← fromGens_coe hI hJ hS h hdp, (fromGens hI hJ hS h hdp).dpow_comp a ha]⟩
  rw [hS, map_span, span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has
/-
**DividedPowers.IsDPMorphism.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers.Is
DPMorphism`。
形式化陈述：of_comp (f : A ->+* B) (g : B ->+* C) (heq : J = I.map f) (hf : IsDPMorphi
sm hI hJ f) (hh : IsDPMorphism hI hK (g.comp f)) : IsDPMorphism hJ hK g
参数：f : A ->+* B；g : B ->+* C；heq : J = I.map f；hf : IsDPMorphism hI hJ f；hh : Is
DPMorphism hI hK (g.comp f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.IsDPMorphism.on_span`：on_span {f : A ->+* B} {S : Set A} (
hS : I = span S) (hS' : forall s in S, f s in J) (hdp : forall {n : Nat}, forall
 a in S, f (hI.dpow n a)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `DividedPowers.IsDPMorphism.ideal_comp`：∀ {A : Type u_1} {B : Type u_2} [
inst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {
hI : DividedPowers I} {hJ :…
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…
-/
theorem of_comp (f : A →+* B) (g : B →+* C) (heq : J = I.map f) (hf : IsDPMorphism hI hJ f)
    (hh : IsDPMorphism hI hK (g.comp f)) : IsDPMorphism hJ hK g := by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply, hh.2 a ha, RingHom.comp_apply, hf.2 a ha]

end IsDPMorphism

namespace DPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} {hI : DividedPowers I} {hJ : DividedPowers J} {hK : DividedPowers K}

/-- The composition of two divided power morphisms as a `DPMorphism`. -/
/-
**DividedPowers.DPMorphism.comp** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.DPMorph
ism`。
形式化陈述：{A : Type u_3} →   {B : Type u_4} →     {C : Type u_5} →       [inst : Com
mSemiring A] →         [inst_1 : CommSemiring B] →           [inst_2 : CommSemir
ing C] →             {I : Ideal A} →               {J : Ideal B} →              
   {K : Ideal C} →                   {hI : DividedPowers I} →                   
  {hJ : DividedPowers J} →                       {hK : DividedPowers K} → hJ.DPM
orphism hK → hI.DPMorphism hJ → hI.DPMorphism hK
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two divided power morphisms as a `DPMorphism`.
-/
protected def comp (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
    DPMorphism hI hK :=
  mk' (IsDPMorphism.comp hK g.isDPMorphism f.isDPMorphism)
/-
**DividedPowers.DPMorphism.comp_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowe
rs.DPMorphism`。
形式化陈述：∀ {A : Type u_3} {B : Type u_4} {C : Type u_5} [inst : CommSemiring A] [in
st_1 : CommSemiring B]   [inst_2 : CommSemiring C] {I : Ideal A} {J : Ideal B} {
K : Ideal C} {hI : DividedPowers I} {hJ : DividedPowers J}   {hK : DividedPowers
 K} (g : hJ.DPMorphism hK) (f : hI.DPMorphism hJ), (g.comp f).toRingHom = g.comp
 f.toRingHom
参数：g : hJ.DPMorphism hK；f : hI.DPMorphism hJ；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_toRingHom (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
    (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom := rfl

end DPMorphism

section Uniqueness

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI hI' : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B}

/-
**DividedPowers.dpow_comp_from_gens** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_comp_from_gens {S : Set A} (hS : I = span S) (hS' : forall s in S, f 
s in J) (hdp : forall {n : Nat}, forall a in S, f (hI.dpow n a) = hJ.dpow n (f a
)) : forall {n}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a)
参数：hS : I = span S；hS' : forall s in S, f s in J；hdp : forall {n : Nat}, forall 
a in S, f (hI.dpow n a) = hJ.dpow n (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.IsDPMorphism.dpow_comp`：∀ {A : Type u_1} {B : Type u_2} [i
nst : CommSemiring A] [inst_1 : CommSemiring B] {I : Ideal A} {J : Ideal B}   {h
I : DividedPowers I} {hJ :…
· 使用定理 `DividedPowers.IsDPMorphism.on_span`：on_span {f : A ->+* B} {S : Set A} (
hS : I = span S) (hS' : forall s in S, f s in J) (hdp : forall {n : Nat}, forall
 a in S, f (hI.dpow n a)…
-/
theorem dpow_comp_from_gens {S : Set A} (hS : I = span S) (hS' : ∀ s ∈ S, f s ∈ J)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    ∀ {n}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  (IsDPMorphism.on_span hI hJ hS hS' hdp).2

/-- If two divided power structures on the ideal `I` agree on a generating set, then they are
  equal.
  See [N. Roby, *Les algèbres à puissances dividées* (Corollary to Proposition 3)][Roby-1965]. -/
/-
**DividedPowers.dpow_eq_from_gens** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers`。
形式化陈述：dpow_eq_from_gens {S : Set A} (hS : I = span S) (hdp : forall {n : Nat}, f
orall a in S, hI.dpow n a = hI'.dpow n a) : hI' = hI
参数：hS : I = span S；hdp : forall {n : Nat}, forall a in S, hI.dpow n a = hI'.dpow
 n a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.ext`：DividedPowers.ext (hI : DividedPowers I) (hI' : Divid
edPowers I) (h_eq : forall (n : Nat) {x : A} (_ : x in I), hI.dpow n x = hI'.dpo
w n x) …
· 使用定理 `DividedPowers.dpow_comp_from_gens`：dpow_comp_from_gens {S : Set A} (hS :
 I = span S) (hS' : forall s in S, f s in J) (hdp : forall {n : Nat}, forall a i
n S, f (hI.dpow n a) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `DividedPowers.dpow_null`：∀ {A : Type u_1} [inst : CommSemiring A] {I : I
deal A} (self : DividedPowers I) {n : ℕ} {x : A},   x ∉ I → self.dpow n x = 0

--- 原说明 ---
If two divided power structures on the ideal `I` agree on a generating set, then
 they are
  equal.
  See [N. Roby, *Les algèbres à puissances dividées* (Corollary to Proposition 3
)][Roby-1965].
-/
theorem dpow_eq_from_gens {S : Set A} (hS : I = span S)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, hI.dpow n a = hI'.dpow n a) : hI' = hI := by
  ext n a
  by_cases ha : a ∈ I
  · refine hI.dpow_comp_from_gens hI' (f := RingHom.id A) hS ?_ ?_ a ha
    · intro s hs
      simp only [RingHom.id_apply, hS]
      exact subset_span hs
    · intro m b hb
      simpa only [RingHom.id_apply] using (hdp b hb)
  · rw [hI.dpow_null ha, hI'.dpow_null ha]

end Uniqueness

end DividedPowers

