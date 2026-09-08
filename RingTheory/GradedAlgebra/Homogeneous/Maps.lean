/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Maps on homogeneous ideals

In this file we define `HomogeneousIdeal.map` and `HomogeneousIdeal.comap`.
-/

@[expose] public section

namespace HomogeneousIdeal

section arbitrary_grading

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)

/-- Map a homogeneous ideal along a graded ring homomorphism. The underlying ideal is
(definitionally) equal to `Ideal.map`. -/
/-
**HomogeneousIdeal.map** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousIdeal`。
形式化陈述：map (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal ℬ where __
参数：I : HomogeneousIdeal 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a homogeneous ideal along a graded ring homomorphism. The underlying ideal i
s
(definitionally) equal to `Ideal.map`.
-/
def map (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal ℬ where
  __ := I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
      exact sum_mem fun ij hij ↦ Ideal.mul_mem_left _ _ <| ih _

/-- Pull back a homogeneous ideal along a graded ring homomorphism.
The underlying ideal is (definitionally) equal to `Ideal.comap`, whose underlying set is
definitionally equal to the preimage. -/
/-
**HomogeneousIdeal.comap** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousIdeal`。
形式化陈述：comap (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where __
参数：I : HomogeneousIdeal ℬ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…

--- 原说明 ---
Pull back a homogeneous ideal along a graded ring homomorphism.
The underlying ideal is (definitionally) equal to `Ideal.comap`, whose underlyin
g set is
definitionally equal to the preimage.
-/
def comap (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap, HomogeneousIdeal.mem_iff, f.map_directSumDecompose]
    exact I.2 _ ha

variable {I I₁ I₂ I₃ : HomogeneousIdeal 𝒜} {J J₁ J₂ J₃ : HomogeneousIdeal ℬ}
  {K : HomogeneousIdeal 𝒞}
/-
**HomogeneousIdeal.map_le_iff_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIde
al`。
形式化陈述：map_le_iff_le_comap : I.map f <= J ↔ I <= J.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
-/
lemma map_le_iff_le_comap : I.map f ≤ J ↔ I ≤ J.comap f := Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap
/-
**HomogeneousIdeal.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：gc_map_comap : GaloisConnection (map f) (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : I.map f <= J
 ↔ I <= J.comap f
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦
  map_le_iff_le_comap f
/-
**HomogeneousIdeal.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4} {τ : Type u_5} {ι : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : AddSubmonoidClass σ A] [inst_5 : AddSubmonoidClass τ B]  
 [inst_6 : DecidableEq ι] [inst_7 : AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ), Monotone (Homogeneous
Ideal.map f)
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `HomogeneousIdeal.gc_map_comap`：gc_map_comap : GaloisConnection (map f) (
comap f)
-/
@[mono, aesop safe apply] lemma map_mono : Monotone (map f) := (gc_map_comap f).monotone_l
/-
**HomogeneousIdeal.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4} {τ : Type u_5} {ι : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : AddSubmonoidClass σ A] [inst_5 : AddSubmonoidClass τ B]  
 [inst_6 : DecidableEq ι] [inst_7 : AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ), Monotone (Homogeneous
Ideal.comap f)
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.comap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `HomogeneousIdeal.gc_map_comap`：gc_map_comap : GaloisConnection (map f) (
comap f)
-/
@[gcongr, mono] lemma comap_mono : Monotone (comap f) := (gc_map_comap f).monotone_u
/-
**HomogeneousIdeal.toIdeal_comap** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4} {τ : Type u_5} {ι : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : AddSubmonoidClass σ A] [inst_5 : AddSubmonoidClass τ B]  
 [inst_6 : DecidableEq ι] [inst_7 : AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) {J : HomogeneousIdeal 
ℬ},   (HomogeneousIdeal.comap f J).toIdeal = Ideal.comap f J.toIdeal
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.comap f J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toIdeal_comap : (J.comap f).toIdeal = J.toIdeal.comap f := rfl
/-
**HomogeneousIdeal.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4} {τ : Type u_5} {ι : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : AddSubmonoidClass σ A] [inst_5 : AddSubmonoidClass τ B]  
 [inst_6 : DecidableEq ι] [inst_7 : AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) {J : HomogeneousIdeal 
ℬ}, ↑(HomogeneousIdeal.comap f J) = ⇑f ⁻¹' ↑J
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.comap f J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_comap : J.comap f = f ⁻¹' J := rfl
/-
**HomogeneousIdeal.toIdeal_map** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4} {τ : Type u_5} {ι : Type u_
7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 : SetLike σ A] [inst_3 : 
SetLike τ B] [inst_4 : AddSubmonoidClass σ A] [inst_5 : AddSubmonoidClass τ B]  
 [inst_6 : DecidableEq ι] [inst_7 : AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [inst_8
 : GradedRing 𝒜]   [inst_9 : GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) {I : HomogeneousIdeal 
𝒜},   (HomogeneousIdeal.map f I).toIdeal = Ideal.map f I.toIdeal
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.map f I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toIdeal_map : (I.map f).toIdeal = I.toIdeal.map f := rfl
/-
**HomogeneousIdeal.isPrime_comap** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
形式化陈述：isPrime_comap [J.toIdeal.IsPrime] : (J.comap f).toIdeal.IsPrime
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isPrime_comap [J.toIdeal.IsPrime] : (J.comap f).toIdeal.IsPrime :=
  inferInstanceAs (J.toIdeal.comap f).IsPrime -- this shows that the simpNF already has the instance
/-
**HomogeneousIdeal.map_id** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_4} {ι : Type u_7} [inst : Semiring A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubmonoidClass σ A] [inst_3 : DecidableEq ι] [ins
t_4 : AddMonoid ι] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜]   {I : HomogeneousIdeal 𝒜
}, HomogeneousIdeal.map (GradedRingHom.id 𝒜) I = I
参数：GradedRingHom.id 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I
-/
@[simp] lemma map_id : I.map (GradedRingHom.id 𝒜) = I := ext <| Ideal.map_id _
/-
**HomogeneousIdeal.map_map** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：map_map : (I.map f).map g = I.map (g.comp f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
-/
lemma map_map : (I.map f).map g = I.map (g.comp f) := ext <| Ideal.map_map _ _
/-
**HomogeneousIdeal.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：map_comp : I.map (g.comp f) = (I.map f).map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomogeneousIdeal.map_map`：map_map : (I.map f).map g = I.map (g.comp f)
-/
lemma map_comp : I.map (g.comp f) = (I.map f).map g := (map_map f g).symm
/-
**HomogeneousIdeal.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_4} {ι : Type u_7} [inst : Semiring A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubmonoidClass σ A] [inst_3 : DecidableEq ι] [ins
t_4 : AddMonoid ι] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜]   {I : HomogeneousIdeal 𝒜
}, HomogeneousIdeal.comap (GradedRingHom.id 𝒜) I = I
参数：GradedRingHom.id 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_id : I.comap (GradedRingHom.id 𝒜) = I := rfl
/-
**HomogeneousIdeal.comap_comap** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：comap_comap : (K.comap g).comap f = K.comap (g.comp f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comap : (K.comap g).comap f = K.comap (g.comp f) := rfl

end arbitrary_grading

section canonical_grading

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {f : 𝒜 →+*ᵍ ℬ} {g : ℬ →+*ᵍ 𝒞}

/-
**HomogeneousIdeal.irrelevant_le_map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Homogeneous
Ideal`。
形式化陈述：irrelevant_le_map_comp (hf : ℬ₊ <= 𝒜₊.map f) (hg : 𝒞₊ <= ℬ₊.map g) : 𝒞₊ <=
 𝒜₊.map (g.comp f)
参数：hf : ℬ₊ <= 𝒜₊.map f；hg : 𝒞₊ <= ℬ₊.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousIdeal.map_comp`：map_comp : I.map (g.comp f) = (I.map f).map g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HomogeneousIdeal.map_mono`：∀ {A : Type u_1} {B : Type u_2} {σ : Type u_4
} {τ : Type u_5} {ι : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]   [ins
t_2 : SetLike σ…
-/
theorem irrelevant_le_map_comp
    (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ ℬ₊.map g) : 𝒞₊ ≤ 𝒜₊.map (g.comp f) := by
  rw [map_comp]
  exact hg.trans <| map_mono _ hf

end canonical_grading

end HomogeneousIdeal

