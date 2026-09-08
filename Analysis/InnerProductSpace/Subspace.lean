/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Subspaces of inner product spaces

This file defines the inner-product structure on a subspace of an inner-product space, and proves
some theorems about orthogonal families of subspaces.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp Module

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Submodule

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
/-
**Submodule.innerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W
参数：W : Submodule 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induced inner product on a submodule.
-/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  fast_instance% .induced W.subtype

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
/-
**Submodule.coe_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫
参数：W : Submodule 𝕜 E；x y : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product on submodules is the same as on the ambient space.
-/
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl
/-
**Orthonormal.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.codRestrict {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (s
 : Submodule 𝕜 E) (hvs : forall i, v i in s) : @Orthonormal 𝕜 s _ _ _ ι (Set.cod
Restrict v s hvs)
参数：hv : Orthonormal 𝕜 v；s : Submodule 𝕜 E；hvs : forall i, v i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearIsometry.orthonormal_comp_iff`：LinearIsometry.orthonormal_comp_iff
 {v : ι -> E} (f : E ->ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v
-/
theorem Orthonormal.codRestrict {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
    (hvs : ∀ i, v i ∈ s) : @Orthonormal 𝕜 s _ _ _ ι (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv
/-
**orthonormal_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_span {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) : @Orthon
ormal 𝕜 (Submodule.span 𝕜 (Set.range v)) _ _ _ ι fun i : ι => ⟨v i, Submodule.su
bset_span (Set.mem_range_self i)⟩
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.codRestrict`：Orthonormal.codRestrict {ι : Type*} {v : ι -> E
} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E) (hvs : forall i, v i in s) : @Ortho
normal 𝕜 s _ …
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem orthonormal_span {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) :
    @Orthonormal 𝕜 (Submodule.span 𝕜 (Set.range v)) _ _ _ ι fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

end Submodule

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/

section OrthogonalFamily_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

open DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → Submodule 𝕜 E`.  We
instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.
The connection to the subobject spelling is shown in `orthogonalFamily_iff_pairwise`.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`PiLp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
/-
**OrthogonalFamily** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrthogonalFamily (G : ι -> Type*) [forall i, SeminormedAddCommGroup (G i)]
 [forall i, InnerProductSpace 𝕜 (G i)] (V : forall i, G i ->ₗᵢ[𝕜] E) : Prop
参数：G : ι -> Type*；G i；G i；V : forall i, G i ->ₗᵢ[𝕜] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An indexed family of mutually-orthogonal subspaces of an inner product space `E`
.

The simple way to express this concept would be as a condition on `V : ι → Submo
dule 𝕜 E`.  We
instead implement it as a condition on a family of inner product spaces each equ
ipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than
 subobjects.
The connection to the subobject spelling is shown in `orthogonalFamily_iff_pairw
ise`.

This definition is less lightweight, but allows for better definitional properti
es when the inner
product space structure on each of the submodules is important -- for example, w
hen considering
their Hilbert sum (`PiLp V 2`).  For example, given an orthonormal set of vector
s `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, whi
ch it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`.
-/
def OrthogonalFamily (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  Pairwise fun i j => ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variable {𝕜}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
  {V : ∀ i, G i →ₗᵢ[𝕜] E}
/-
**Orthonormal.orthogonalFamily** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.orthogonalFamily {v : ι -> E} (hv : Orthonormal 𝕜 v) : Orthogo
nalFamily 𝕜 (fun _i : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 
i)
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Orthonormal.orthogonalFamily {v : ι → E} (hv : Orthonormal 𝕜 v) :
    OrthogonalFamily 𝕜 (fun _i : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

section
variable (hV : OrthogonalFamily 𝕜 G V)
include hV

/-
**OrthogonalFamily.eq_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.eq_ite [DecidableEq ι] {i j : ι} (v : G i) (w : G j) : ⟪V
 i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0
参数：v : G i；w : G j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem OrthogonalFamily.eq_ite [DecidableEq ι] {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 := by
  split_ifs with h
  · rfl
  · exact hV h v w

set_option backward.isDefEq.respectTransparency false in
/-
**OrthogonalFamily.inner_right_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.inner_right_dfinsupp [forall (i) (x : G i), Decidable (x 
!= 0)] [DecidableEq ι] (l : ⨁ i, G i) (i : ι) (v : G i) : ⟪V i v, l.sum fun j =>
 V j⟫ = ⟪v, l i⟫
参数：i；x : G i；x != 0；l : ⨁ i, G i；i : ι；v : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.inner_sum`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u
_4} [ins…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrthogonalFamily.eq_ite`：OrthogonalFamily.eq_ite [DecidableEq ι] {i j : 
ι} (v : G i) (w : G j) : ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
-/
theorem OrthogonalFamily.inner_right_dfinsupp
    [∀ (i) (x : G i), Decidable (x ≠ 0)] [DecidableEq ι] (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j => fun w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun _ => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, Finset.sum_ite_eq,
        DFinsupp.mem_support_toFun]
      split_ifs with h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]
/-
**OrthogonalFamily.inner_right_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.inner_right_fintype [Fintype ι] (l : forall i, G i) (i : 
ι) (v : G i) : ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫
参数：l : forall i, G i；i : ι；v : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrthogonalFamily.eq_ite`：OrthogonalFamily.eq_ite [DecidableEq ι] {i j : 
ι} (v : G i) (w : G j) : ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]

nonrec theorem OrthogonalFamily.inner_sum (l₁ l₂ : ∀ i, G i) (s : Finset ι) :
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
  classical
  calc
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ j ∈ s, ∑ i ∈ s, ⟪V i (l₁ i), V j (l₂ j)⟫ := by
      simp only [sum_inner, inner_sum]
    _ = ∑ j ∈ s, ∑ i ∈ s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 := by
      congr with i
      congr with j
      apply hV.eq_ite
    _ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
      simp only [Finset.sum_ite_of_true, Finset.sum_ite_eq', LinearIsometry.inner_map_map,
        imp_self, imp_true_iff]
/-
**OrthogonalFamily.norm_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.norm_sum (l : forall i, G i) (s : Finset ι) : ‖∑ i in s, 
V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2
参数：l : forall i, G i；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthogonalFamily.inner_sum`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι 
: Type u_4} {G :…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) :
    ‖∑ i ∈ s, V i (l i)‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  have : ((‖∑ i ∈ s, V i (l i)‖ : ℝ) : 𝕜) ^ 2 = ∑ i ∈ s, ((‖l i‖ : ℝ) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
/-
**OrthogonalFamily.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.comp {γ : Type*} {f : γ -> ι} (hf : Function.Injective f)
 : OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f g)
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
The composition of an orthogonal family of subspaces with an injective function 
is also an
orthogonal family.
-/
theorem OrthogonalFamily.comp {γ : Type*} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f g) :=
  fun _i _j hij v w => hV (hf.ne hij) v w
/-
**OrthogonalFamily.orthonormal_sigma_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι -> Type*} {v_family 
: forall i, α i -> G i} (hv_family : forall i, Orthonormal 𝕜 (v_family i)) : Ort
honormal 𝕜 fun a : Σ i, α i => V a.1 (v_family a.1 a.2)
参数：hv_family : forall i, Orthonormal 𝕜 (v_family i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σ i, α i => V a.1 (v_family a.1 a.2) := by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v ≠ w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)
/-
**OrthogonalFamily.norm_sq_sdiff_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.norm_sq_sdiff_sum [DecidableEq ι] (f : forall i, G i) (s₁
 s₂ : Finset ι) : ‖(∑ i in s₁, V i (f i)) - ∑ i in s₂, V i (f i)‖ ^ 2 = (∑ i in 
s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2
参数：f : forall i, G i；s₁ s₂ : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff_sub_sum_sdiff`：∀ {ι : Type u_1} {G : Type u_3} {s₁ s₂ :
 Finset ι} [inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G},   ∑ x ∈
 s₂ \ s₁, f x - ∑ x …
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `disjoint_sdiff_sdiff`：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `OrthogonalFamily.norm_sum`：OrthogonalFamily.norm_sum (l : forall i, G i)
 (s : Finset ι) : ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearIsometry.map_neg`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} 
{E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [i
nst_2 : Semi…
-/
theorem OrthogonalFamily.norm_sq_sdiff_sum [DecidableEq ι] (f : ∀ i, G i) (s₁ s₂ : Finset ι) :
    ‖(∑ i ∈ s₁, V i (f i)) - ∑ i ∈ s₂, V i (f i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  let F : ∀ i, G i := fun i => if i ∈ s₁ then f i else -f i
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = -f i := fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
  have hF : ∀ i, ‖F i‖ = ‖f i‖ := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [norm_neg]
  have :
    ‖(∑ i ∈ s₁ \ s₂, V i (F i)) + ∑ i ∈ s₂ \ s₁, V i (F i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖F i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖F i‖ ^ 2 := by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁)
  convert! this using 4
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₁ i hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₂ i hi, LinearIsometry.map_neg]
  · simp only [hF]
  · simp only [hF]

@[deprecated (since := "2026-06-03")]
alias OrthogonalFamily.norm_sq_diff_sum := OrthogonalFamily.norm_sq_sdiff_sum

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(fun i ↦ ‖f i‖ ^ 2)` is summable. -/
/-
**OrthogonalFamily.summable_iff_norm_sq_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : fora
ll i, G i) : (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2
参数：f : forall i, G i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg_add`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), ‖-a + b‖ = ‖a - b‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_pos`：sqrt_pos : 0 < √x ↔ 0 < x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff_sub_sum_sdiff`：∀ {ι : Type u_1} {G : Type u_3} {s₁ s₂ :
 Finset ι} [inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G},   ∑ x ∈
 s₂ \ s₁, f x - ∑ x …
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder 
G] [IsOrderedAddMonoid G] (a b : G), |a - b| ≤ |a| + |b|
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.abs_sum_of_nonneg'`：abs_sum_of_nonneg' {G : Type*} [AddCommGroup 
G] [LinearOrder G] [AddLeftMono G] {f : ι -> G} {s : Finset ι} (hf : forall i, 0
 <= f i) : |∑ i…
· 使用定理 `OrthogonalFamily.norm_sq_sdiff_sum`：OrthogonalFamily.norm_sq_sdiff_sum [
DecidableEq ι] (f : forall i, G i) (s₁ s₂ : Finset ι) : ‖(∑ i in s₁, V i (f i)) 
- ∑ i in s₂, V i (f i)‖ …
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 120 条，此处仅展示前 30 条）

--- 原说明 ---
A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(fun i ↦ ‖f i‖ ^ 2)` is summable.
-/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : ∀ i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, norm_neg_add,
      Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
      refine (abs_sub _ _).trans_lt ?_
      have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2) < √ε ^ 2 := by
        rw [← hV.norm_sq_sdiff_sum, sq_lt_sq, abs_of_nonneg (sqrt_nonneg _),
          abs_of_nonneg (norm_nonneg _)]
        exact H s₁ hs₁ s₂ hs₂
      have hη := sq_sqrt (le_of_lt hε)
      linarith
    · intro hf ε hε
      have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
      obtain ⟨a, H⟩ := hf _ hε'
      use a
      intro s₁ hs₁ s₂ hs₂
      refine (abs_lt_of_sq_lt_sq' ?_ (le_of_lt hε)).2
      have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂
      rw [hV.norm_sq_sdiff_sum]
      have Hs₁ : ∑ x ∈ s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₁ _ has
        have : s₁ ⊓ s₂ ⊆ s₁ := Finset.inter_subset_left
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      have Hs₂ : ∑ x ∈ s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₂ _ has
        have : s₁ ⊓ s₂ ⊆ s₂ := Finset.inter_subset_right
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      linarith

end

end OrthogonalFamily_Seminormed

section OrthogonalFamily

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} {G : ι → Type*}

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
/-
**OrthogonalFamily.independent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.independent {V : ι -> Submodule 𝕜 E} (hV : OrthogonalFami
ly 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : iSupIndep V
参数：hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep_of_dfinsupp_lsum_injective`：iSupIndep_of_dfinsupp_lsum_injecti
ve (p : ι -> Submodule R N) (h : Function.Injective (lsum Nat fun i => (p i).sub
type)) : iSupIndep p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthogonalFamily.inner_right_dfinsupp`：OrthogonalFamily.inner_right_dfin
supp [forall (i) (x : G i), Decidable (x != 0)] [DecidableEq ι] (l : ⨁ i, G i) (
i : ι) (v : G i) : ⟪V i v, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An orthogonal family forms an independent family of subspaces; that is, any coll
ection of
elements each from a different subspace in the family is linearly independent. I
n particular, the
pairwise intersections of elements of the family are 0.
-/
theorem OrthogonalFamily.independent {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    iSupIndep V := by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using! this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFinsupp.lsum ℕ (fun i => (V i).subtype) v⟫ := by
      simpa only [DFinsupp.sumAddHom_apply, DFinsupp.lsum_apply_apply] using!
        (hV.inner_right_dfinsupp v i (v i)).symm
    _ = 0 := by simp only [hv, inner_zero_right]
/-
**DirectSum.IsInternal.collectedBasis_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.collectedBasis_orthonormal [DecidableEq ι] {V : ι -> 
Submodule 𝕜 E} (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
 (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι -> Type*} {v_family : foral
l i, Basis (α i) 𝕜 (V i)} (hv_family : forall i, Orthonormal 𝕜 (v_family i)) : O
rthonormal 𝕜 (hV_sum.collectedBasis v_family)
参数：hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ；hV_sum : Dire
ctSum.IsInternal fun i => V i；α i；V i；hv_family : forall i, Orthonormal 𝕜 (v_fam
ily i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
· 使用定理 `OrthogonalFamily.orthonormal_sigma_orthonormal`：OrthogonalFamily.orthono
rmal_sigma_orthonormal {α : ι -> Type*} {v_family : forall i, α i -> G i} (hv_fa
mily : forall i, Orthonormal 𝕜 (v_fa…
-/
theorem DirectSum.IsInternal.collectedBasis_orthonormal [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type*}
    {v_family : ∀ i, Basis (α i) 𝕜 (V i)} (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collectedBasis_coe] using! hV.orthonormal_sigma_orthonormal hv_family

end OrthogonalFamily

