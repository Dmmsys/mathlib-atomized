/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/

public section

open Polynomial Submodule

section Ring

variable {R S A T : Type*}
variable [CommRing R] [Ring A] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
variable [Algebra R A]

/-
**RingHom.isIntegralElem_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩
/-
**isIntegral_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
-/
theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

variable {f} in
/-
**RingHom.IsIntegralElem.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.map {x : S} (hx : f.IsIntegralElem x) (g : S ->+* T
) : (g.comp f).IsIntegralElem (g x)
参数：hx : f.IsIntegralElem x；g : S ->+* T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.IsIntegralElem.map {x : S} (hx : f.IsIntegralElem x) (g : S →+* T) :
    (g.comp f).IsIntegralElem (g x) := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

variable {f g} in
/-
**RingHom.IsIntegralElem.of_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.of_map (hg : Function.Injective g) {x : S} (hx : (g
.comp f).IsIntegralElem (g x)) : f.IsIntegralElem x
参数：hg : Function.Injective g；hx : (g.comp f).IsIntegralElem (g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.IsIntegralElem.of_map (hg : Function.Injective g) {x : S}
    (hx : (g.comp f).IsIntegralElem (g x)) :
    f.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, hg <| by simp [Polynomial.hom_eval₂, hx]⟩

variable {f g} in
/-
**RingHom.IsIntegralElem.map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.map_iff (hg : Function.Injective g) {x : S} : (g.co
mp f).IsIntegralElem (g x) ↔ f.IsIntegralElem x
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsIntegralElem.of_map`：RingHom.IsIntegralElem.of_map (hg : Funct
ion.Injective g) {x : S} (hx : (g.comp f).IsIntegralElem (g x)) : f.IsIntegralEl
em x
· 使用引理 `RingHom.IsIntegralElem.map`：RingHom.IsIntegralElem.map {x : S} (hx : f.I
sIntegralElem x) (g : S ->+* T) : (g.comp f).IsIntegralElem (g x)
-/
lemma RingHom.IsIntegralElem.map_iff (hg : Function.Injective g) {x : S} :
    (g.comp f).IsIntegralElem (g x) ↔ f.IsIntegralElem x :=
  ⟨of_map hg, (map · g)⟩

end Ring

section

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [Ring T]
variable [Algebra R A] (f : R →+* S)

variable {f} in
/-
**RingHom.IsIntegralElem.of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.of_comp {g : S ->+* T} {x : T} (hx : (g.comp f).IsI
ntegralElem x) : g.IsIntegralElem x
参数：hx : (g.comp f).IsIntegralElem x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
lemma RingHom.IsIntegralElem.of_comp {g : S →+* T} {x : T} (hx : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, map_map] using hx⟩
/-
**IsIntegral.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A 
B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : 
B} [FunLike F B C] [AlgHomClass F A B C] (f : F) (hb : IsIntegral R b) : IsInteg
ral R (f b)
参数：f : F；hb : IsIntegral R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegral.eq_1`：∀ (R : Type u_1) {A : Type u_3} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   IsIntegral R x = (algebraMap R 
A).Is…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用引理 `RingHom.IsIntegralElem.map`：RingHom.IsIntegralElem.map {x : S} (hx : f.I
sIntegralElem x) (g : S ->+* T) : (g.comp f).IsIntegralElem (g x)
-/
theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  rw [IsIntegral, ← ((AlgHomClass.toAlgHom f).restrictScalars R).comp_algebraMap]
  exact .map hb (RingHomClass.toRingHom f)

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-
**isIntegral_algHom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Function.Injective f) {x : A}
 : IsIntegral R (f x) ↔ IsIntegral R x
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.IsIntegralElem.map_iff`：RingHom.IsIntegralElem.map_iff (hg : Fun
ction.Injective g) {x : S} : (g.comp f).IsIntegralElem (g x) ↔ f.IsIntegralElem 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isIntegral_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A} :
    IsIntegral R (f x) ↔ IsIntegral R x := by
  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A →+* B)) hf]

end

open scoped Classical in
/-
**Submodule.span_range_natDegree_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [
Algebra R A] {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) : span R (F
inset.image (x ^ ·) (Finset.range (natDegree f))) = Subalgebra.toSubmodule (Alge
bra.adjoin R {x})
参数：hf : f.Monic；hfx : aeval x f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用定理 `Algebra.adjoin_singleton_eq_range_aeval`：adjoin_singleton_eq_range_aeval
 (x : A) : adjoin R {x} = (aeval x).range
· 使用定理 `Subalgebra.mem_toSubmodule`：mem_toSubmodule {x} : x in (toSubmodule S) ↔
 x in S
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
（共 51 条，此处仅展示前 30 条）
-/
theorem Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A]
    {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree f))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality A
  have hf1 : f ≠ 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs ↦ ?_).antisymm fun r hr ↦ ?_
  · rcases Finset.mem_image.1 (SetLike.mem_coe.mp hs) with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p f, map_add, map_mul, hfx,
      zero_mul, add_zero, ← sum_C_mul_X_pow_eq (p %ₘ f), aeval_def, eval₂_sum, sum_def]
  refine sum_mem fun k hkq ↦ ?_
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial, ← Algebra.smul_def]
  exact smul_mem _ _ (subset_span <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <|
    (le_natDegree_of_mem_supp _ hkq).trans_lt <| natDegree_modByMonic_lt p hf hf1)
/-
**IsIntegral.fg_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x)
 : (Algebra.adjoin R {x}).toSubmodule.FG
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_range_natDegree_eq_adjoin`：Submodule.span_range_natDegree
_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A] {x : A} {f : R[X]} (hf 
: f.Monic) (hfx : aeval x f = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
-/
theorem IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x) :
    (Algebra.adjoin R {x}).toSubmodule.FG := by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

variable (f : R →+* B)
/-
**RingHom.isIntegralElem_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegralElem_zero : f.IsIntegralElem 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem RingHom.isIntegralElem_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.isIntegralElem_map
/-
**isIntegral_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_zero`：RingHom.isIntegralElem_zero : f.IsIntegralE
lem 0
-/
theorem isIntegral_zero [Algebra R B] : IsIntegral R (0 : B) :=
  (algebraMap R B).isIntegralElem_zero
/-
**RingHom.isIntegralElem_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegralElem_one : f.IsIntegralElem 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem RingHom.isIntegralElem_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.isIntegralElem_map
/-
**isIntegral_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_one [Algebra R B] : IsIntegral R (1 : B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_one`：RingHom.isIntegralElem_one : f.IsIntegralEle
m 1
-/
theorem isIntegral_one [Algebra R B] : IsIntegral R (1 : B) :=
  (algebraMap R B).isIntegralElem_one

variable (f : R →+* S)
/-
**IsIntegral.of_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn : 0 < n) (hx : IsInt
egral R <| x ^ n) : IsIntegral R x
参数：hn : 0 < n；hx : IsIntegral R <| x ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.expand`：∀ {R : Type u} [inst : CommSemiring R] {p : ℕ} 
{f : Polynomial R}, 0 < p → f.Monic → ((Polynomial.expand R p) f).Monic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.expand_aeval`：expand_aeval {A : Type*} [Semiring A] [Algebra 
R A] (p : Nat) (P : R[X]) (r : A) : aeval r (expand R p P) = aeval (r ^ p) P
-/
theorem IsIntegral.of_pow [Algebra R B] {x : B} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩
/-
**IsIntegral.of_aeval_monic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_aeval_monic {x : A} {p : R[X]} (monic : p.Monic) (deg : p.na
tDegree != 0) (hx : IsIntegral R (aeval x p)) : IsIntegral R x
参数：monic : p.Monic；deg : p.natDegree != 0；hx : IsIntegral R (aeval x p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.Monic.comp`：comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegr
ee != 0) : (p.comp q).Monic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_comp`：eval₂_comp {x : S} : eval₂ f x (p.comp q) = eval₂
 f (eval₂ f x q) p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
-/
theorem IsIntegral.of_aeval_monic {x : A} {p : R[X]} (monic : p.Monic)
    (deg : p.natDegree ≠ 0) (hx : IsIntegral R (aeval x p)) : IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨_, hmonic.comp monic deg, by rwa [eval₂_comp, ← aeval_def x]⟩

end

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

/-
**IsIntegral.map_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S] [CommRin
g T] [Ring U] [Algebra R S] [Algebra T U] (φ : R ->+* T) (ψ : S ->+* U) (h : (al
gebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) : 
IsIntegral T (ψ a)
参数：φ : R ->+* T；ψ : S ->+* U；h : (algebraMap T U).comp φ = ψ.comp (algebraMap R 
S)；ha : IsIntegral R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.eval₂_at_apply`：eval₂_at_apply {S : Type*} [Semiring S] (f : 
R ->+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S]
    [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R →+* T) (ψ : S →+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) :=
  let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply, eval_map, hp.2, ψ.map_zero]⟩

@[simp]
/-
**isIntegral_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra
 R B] (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
参数：f : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h ↦ by simpa using h.map f.symm, IsIntegral.map f⟩

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
/-
**IsIntegral.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B} (hx : IsI
ntegral R x) : IsIntegral A x
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p

--- 原说明 ---
If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`.
-/
theorem IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B}
    (hx : IsIntegral R x) : IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p.map <| algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

/-- If `R` and `T` are isomorphic commutative rings and `S` is an `R`-algebra and a `T`-algebra in
a compatible way, then an element `a ∈ S` is integral over `R` if and only if it is integral
over `T`. -/
/-
**RingEquiv.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingEquiv.isIntegral_iff {R S T : Type*} [CommRing R] [Ring S] [CommRing T
] [Algebra R S] [Algebra T S] (φ : R ≃+* T) (h : (algebraMap T S).comp φ.toRingH
om = algebraMap R S) (a : S) : IsIntegral R a ↔ IsIntegral T a
参数：φ : R ≃+* T；h : (algebraMap T S).comp φ.toRingHom = algebraMap R S；a : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `R` and `T` are isomorphic commutative rings and `S` is an `R`-algebra and a 
`T`-algebra in
a compatible way, then an element `a ∈ S` is integral over `R` if and only if it
 is integral
over `T`.
-/
theorem RingEquiv.isIntegral_iff {R S T : Type*} [CommRing R] [Ring S] [CommRing T]
    [Algebra R S] [Algebra T S] (φ : R ≃+* T)
    (h : (algebraMap T S).comp φ.toRingHom = algebraMap R S) (a : S) :
    IsIntegral R a ↔ IsIntegral T a := by
  constructor <;> intro ha
  · let : Algebra R T := φ.toRingHom.toAlgebra
    let : IsScalarTower R T S :=
      ⟨fun r t s ↦ by simp only [Algebra.smul_def, map_mul, ← h, mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
  · have h' : (algebraMap T S) = (algebraMap R S).comp φ.symm.toRingHom := by
      have : RingHomInvPair (φ : R →+* T) φ.symm := RingHomInvPair.of_ringEquiv _
      simp only [← h, RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq]
    let : Algebra T R := φ.symm.toRingHom.toAlgebra
    let : IsScalarTower T R S :=
      ⟨fun r t s ↦ by simp only [Algebra.smul_def, map_mul, h', mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
/-
**map_isIntegral_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B} [FunLike F B 
C] [RingHomClass F B C] (f : F) (hb : IsIntegral Int b) : IsIntegral Int (f b)
参数：f : F；hb : IsIntegral Int b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
-/
theorem map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B}
    [FunLike F B C] [RingHomClass F B C] (f : F)
    (hb : IsIntegral ℤ b) : IsIntegral ℤ (f b) :=
  hb.map (f : B →+* C).toIntAlgHom
/-
**IsIntegral.of_subring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_subring {x : B} (T : Subring R) (hx : IsIntegral T x) : IsIn
tegral R x
参数：T : Subring R；hx : IsIntegral T x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Submonoid.instIsScalarTowerSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul α 
β]   [inst_2 : SMul M' α] […
-/
theorem IsIntegral.of_subring {x : B} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  hx.tower_top
/-
**IsIntegral.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegral`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R A] [inst_4 : Algebra R B]
 [inst_5 : Algebra A B] [IsScalarTower R A B] {x : A},   IsIntegral R x → IsInte
gral R ((algebraMap A B) x)
参数：(algebraMap A B) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected theorem IsIntegral.algebraMap [Algebra A B] [IsScalarTower R A B] {x : A}
    (h : IsIntegral R x) : IsIntegral R (algebraMap A B x) := by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B, ← hom_eval₂, hx, map_zero]
/-
**isIntegral_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A} (hAB
 : Function.Injective (algebraMap A B)) : IsIntegral R (algebraMap A B x) ↔ IsIn
tegral R x
参数：hAB : Function.Injective (algebraMap A B)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
-/
theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
    (hAB : Function.Injective (algebraMap A B)) :
    IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB
/-
**isIntegral_iff_isIntegral_closure_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_iff_isIntegral_closure_finite {r : B} : IsIntegral R r ↔ exists
 s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.monic_restriction`：monic_restriction {p : R[X]} : Monic (rest
riction p) ↔ Monic p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `Submonoid.instIsScalarTowerSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul α 
β]   [inst_2 : SMul M' α] […
· 使用定理 `Polynomial.map_restriction`：map_restriction {R : Type u} [CommRing R] (p
 : R[X]) : p.restriction.map (algebraMap _ _) = p
· 使用定理 `IsIntegral.of_subring`：IsIntegral.of_subring {x : B} (T : Subring R) (hx
 : IsIntegral T x) : IsIntegral R x
-/
theorem isIntegral_iff_isIntegral_closure_finite {r : B} :
    IsIntegral R r ↔ ∃ s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r := by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap R r p.restriction, map_restriction, aeval_def, hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hsr.of_subring _

@[stacks 09GH]
/-
**fg_adjoin_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : forall x in s, IsI
ntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
参数：hfs : s.Finite；his : forall x in s, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.adjoin_union_coe_submodule`：adjoin_union_coe_submodule : Subalge
bra.toSubmodule (adjoin R (s union t)) = Subalgebra.toSubmodule (adjoin R s) * S
ubalgebra.toSubmodule (a…
· 使用定理 `Submodule.FG.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M N : Submodule R A}, M.FG → N
.FG → …
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : ∀ x ∈ s, IsIntegral R x) :
    (Algebra.adjoin R s).toSubmodule.FG := by
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    refine ⟨{1}, Submodule.ext fun x => ?_⟩
    rw [Algebra.adjoin_empty, Finset.coe_singleton, ← one_eq_span, Algebra.toSubmodule_bot]
  | @insert a s _ _ ih =>
    rw [← Set.union_singleton, Algebra.adjoin_union_coe_submodule]
    exact FG.mul
      (ih fun i hi => his i <| Set.mem_insert_of_mem a hi)
      (his a <| Set.mem_insert a s).fg_adjoin_singleton
/-
**Algebra.finite_adjoin_of_finite_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.finite_adjoin_of_finite_of_isIntegral {s : Set A} (hf : s.Finite) 
(hi : forall x in s, IsIntegral R x) : Module.Finite R (adjoin R s)
参数：hf : s.Finite；hi : forall x in s, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
-/
theorem Algebra.finite_adjoin_of_finite_of_isIntegral {s : Set A} (hf : s.Finite)
    (hi : ∀ x ∈ s, IsIntegral R x) : Module.Finite R (adjoin R s) :=
  .of_fg <| fg_adjoin_of_finite hf hi
/-
**Algebra.finite_adjoin_simple_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.finite_adjoin_simple_of_isIntegral {x : B} (hi : IsIntegral R x) :
 Module.Finite R (adjoin R {x})
参数：hi : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
-/
theorem Algebra.finite_adjoin_simple_of_isIntegral {x : B} (hi : IsIntegral R x) :
    Module.Finite R (adjoin R {x}) :=
  .of_fg hi.fg_adjoin_singleton
/-
**isNoetherian_adjoin_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A) (hs : foral
l x in s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (s : Set A))
参数：s : Finset A；hs : forall x in s, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_fg_of_noetherian`：isNoetherian_of_fg_of_noetherian {R M}
 [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) [I : IsNoetherianRin
g R] (hN : N.FG) : IsN…
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (s : Set A)) :=
  isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

end

section Prod

variable {R A B : Type*}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- An element of a product algebra is integral if each component is integral. -/
/-
**IsIntegral.pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (hx₂ : IsIntegral R x
.2) : IsIntegral R x
参数：hx₁ : IsIntegral R x.1；hx₂ : IsIntegral R x.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.aeval_prod_apply`：aeval_prod_apply (x : A × B) (p : Polynomia
l R) : p.aeval x = (p.aeval x.1, p.aeval x.2)
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Prod.zero_eq_mk`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst_1
 : Zero N], 0 = (0, 0)

--- 原说明 ---
An element of a product algebra is integral if each component is integral.
-/
theorem IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (hx₂ : IsIntegral R x.2) :
    IsIntegral R x := by
  obtain ⟨p₁, ⟨hp₁Monic, hp₁Eval⟩⟩ := hx₁
  obtain ⟨p₂, ⟨hp₂Monic, hp₂Eval⟩⟩ := hx₂
  refine ⟨p₁ * p₂, ⟨hp₁Monic.mul hp₂Monic, ?_⟩⟩
  rw [← aeval_def] at *
  rw [aeval_prod_apply, aeval_mul, hp₁Eval, zero_mul, aeval_mul, hp₂Eval, mul_zero,
    Prod.zero_eq_mk]

/-- An element of a product algebra is integral iff each component is integral. -/
/-
**IsIntegral.pair_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.pair_iff {x : A × B} : IsIntegral R x ↔ IsIntegral R x.1 ∧ IsIn
tegral R x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `IsIntegral.pair`：IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (h
x₂ : IsIntegral R x.2) : IsIntegral R x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
An element of a product algebra is integral iff each component is integral.
-/
theorem IsIntegral.pair_iff {x : A × B} : IsIntegral R x ↔ IsIntegral R x.1 ∧ IsIntegral R x.2 :=
  ⟨fun h ↦ ⟨h.map (AlgHom.fst R A B), h.map (AlgHom.snd R A B)⟩, fun h ↦ h.1.pair h.2⟩

end Prod

