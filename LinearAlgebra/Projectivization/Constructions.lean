/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!

# Dot Product and Cross Product on Projective Spaces

This file defines the dot product and cross product on projective spaces.

## Definitions
- `Projectivization.orthogonal v w` is defined as vanishing of the dot product.
- `Projectivization.cross v w` for `v w : ℙ F (Fin 3 → F)` is defined as the cross product of
  `v` and `w` provided that `v ≠ w`. If `v = w`, then the cross product would be zero, so we
  instead define `cross v v = v`.

-/

@[expose] public section

variable {F : Type*} [Field F] {m : Type*} [Fintype m]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section DotProduct

/-- Orthogonality on the projective plane. -/
/-
**Projectivization.orthogonal** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：orthogonal : ℙ F (m -> F) -> ℙ F (m -> F) -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Orthogonality on the projective plane.
-/
def orthogonal : ℙ F (m → F) → ℙ F (m → F) → Prop :=
  Quotient.lift₂ (fun v w ↦ v.1 ⬝ᵥ w.1 = 0) (fun _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ by
    simp_rw [← h1, ← h2, dotProduct_smul, smul_dotProduct, smul_smul,
      smul_eq_zero_iff_eq])
/-
**Projectivization.orthogonal_mk** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：orthogonal_mk {v w : m -> F} (hv : v != 0) (hw : w != 0) : orthogonal (mk 
F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0
参数：hv : v != 0；hw : w != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma orthogonal_mk {v w : m → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    orthogonal (mk F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0 :=
  Iff.rfl
/-
**Projectivization.orthogonal_comm** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：orthogonal_comm {v w : ℙ F (m -> F)} : orthogonal v w ↔ orthogonal w v
参数：m -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.orthogonal_mk`：orthogonal_mk {v w : m -> F} (hv : v != 
0) (hw : w != 0) : orthogonal (mk F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma orthogonal_comm {v w : ℙ F (m → F)} : orthogonal v w ↔ orthogonal w v := by
  induction v with | h v hv => induction w with | h w hw =>
  rw [orthogonal_mk hv hw, orthogonal_mk hw hv, dotProduct_comm]
/-
**Projectivization.exists_not_self_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Project
ivization`。
形式化陈述：exists_not_self_orthogonal (v : ℙ F (m -> F)) : exists w, ¬ orthogonal v w
参数：v : ℙ F (m -> F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dotProduct_eq_zero_iff`：dotProduct_eq_zero_iff {v : n -> R} : (forall w,
 v ⬝ᵥ w = 0) ↔ v = 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
-/
lemma exists_not_self_orthogonal (v : ℙ F (m → F)) : ∃ w, ¬ orthogonal v w := by
  induction v with | h v hv =>
  rw [ne_eq, ← dotProduct_eq_zero_iff, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨mk F w fun h ↦ hw (by rw [h, dotProduct_zero]), hw⟩
/-
**Projectivization.exists_not_orthogonal_self** 是 Mathlib 中的一个引理，位于命名空间 `Project
ivization`。
形式化陈述：exists_not_orthogonal_self (v : ℙ F (m -> F)) : exists w, ¬ orthogonal w v
参数：v : ℙ F (m -> F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Projectivization.exists_not_self_orthogonal`：exists_not_self_orthogonal 
(v : ℙ F (m -> F)) : exists w, ¬ orthogonal v w
-/
lemma exists_not_orthogonal_self (v : ℙ F (m → F)) : ∃ w, ¬ orthogonal w v := by
  simp only [orthogonal_comm]
  exact exists_not_self_orthogonal v

end DotProduct

section CrossProduct

/-
**Projectivization.mk_eq_mk_iff_crossProduct_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `
Projectivization`。
形式化陈述：mk_eq_mk_iff_crossProduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w
 != 0) : mk F v hv = mk F w hw ↔ crossProduct v w = 0
参数：hv : v != 0；hw : w != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Projectivization.mk_eq_mk_iff'`：mk_eq_mk_iff' (v w : V) (hv : v != 0) (h
w : w != 0) : mk K v hv = mk K w hw ↔ exists a : K, a • w = v
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `LinearIndependent.pair_iff'`：LinearIndependent.pair_iff' {x y : V} (hx :
 x != 0) : LinearIndependent K ![x, y] ↔ forall a : K, a • x != y
· 使用引理 `crossProduct_ne_zero_iff_linearIndependent`：crossProduct_ne_zero_iff_lin
earIndependent {F : Type*} [Field F] {v w : Fin 3 -> F} : crossProduct v w != 0 
↔ LinearIndependent F ![v, w]
· 使用定理 `cross_anticomm`：cross_anticomm (v w : Fin 3 -> R) : -(v ⨯₃ w) = w ⨯₃ v
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_eq_mk_iff_crossProduct_eq_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk F v hv = mk F w hw ↔ crossProduct v w = 0 := by
  rw [← not_iff_not, mk_eq_mk_iff', not_exists, ← LinearIndependent.pair_iff' hw,
    ← crossProduct_ne_zero_iff_linearIndependent, ← cross_anticomm, neg_ne_zero]

variable [DecidableEq F]

/-- Cross product on the projective plane. -/
/-
**Projectivization.cross** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：cross : ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F) -> ℙ F (Fin 3 -> F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cross product on the projective plane.
-/
def cross : ℙ F (Fin 3 → F) → ℙ F (Fin 3 → F) → ℙ F (Fin 3 → F) :=
  Quotient.map₂ (fun v w ↦ if h : crossProduct v.1 w.1 = 0 then v else ⟨crossProduct v.1 w.1, h⟩)
    (fun _ _ ⟨a, ha⟩ _ _ ⟨b, hb⟩ ↦ by
      simp_rw [← ha, ← hb, LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_smul,
        mul_comm b a, smul_eq_zero_iff_eq]
      split_ifs
      · use a
      · use a * b)
/-
**Projectivization.cross_mk** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：cross_mk {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : cross (mk F v hv
) (mk F w hw) = if h : crossProduct v w = 0 then mk F v hv else mk F (crossProdu
ct v w) h
参数：hv : v != 0；hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma cross_mk {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    cross (mk F v hv) (mk F w hw) =
      if h : crossProduct v w = 0 then mk F v hv else mk F (crossProduct v w) h := by
  change Quotient.mk'' _ = _
  split_ifs with h <;> simp only [h] <;> rfl
/-
**Projectivization.cross_mk_of_cross_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Projecti
vization`。
形式化陈述：cross_mk_of_cross_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (
h : crossProduct v w = 0) : cross (mk F v hv) (mk F w hw) = mk F v hv
参数：hv : v != 0；hw : w != 0；h : crossProduct v w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk`：cross_mk {v w : Fin 3 -> F} (hv : v != 0) (hw
 : w != 0) : cross (mk F v hv) (mk F w hw) = if h : crossProduct v w = 0 then mk
 F v hv else mk…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma cross_mk_of_cross_eq_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : crossProduct v w = 0) :
    cross (mk F v hv) (mk F w hw) = mk F v hv := by
  rw [cross_mk, dif_pos h]
/-
**Projectivization.cross_mk_of_cross_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Projecti
vization`。
形式化陈述：cross_mk_of_cross_ne_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (
h : crossProduct v w != 0) : cross (mk F v hv) (mk F w hw) = mk F (crossProduct 
v w) h
参数：hv : v != 0；hw : w != 0；h : crossProduct v w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk`：cross_mk {v w : Fin 3 -> F} (hv : v != 0) (hw
 : w != 0) : cross (mk F v hv) (mk F w hw) = if h : crossProduct v w = 0 then mk
 F v hv else mk…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma cross_mk_of_cross_ne_zero {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : crossProduct v w ≠ 0) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w) h := by
  rw [cross_mk, dif_neg h]
/-
**Projectivization.cross_self** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：cross_self (v : ℙ F (Fin 3 -> F)) : cross v v = v
参数：v : ℙ F (Fin 3 -> F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk_of_cross_eq_zero`：cross_mk_of_cross_eq_zero {v
 w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (h : crossProduct v w = 0) : cross 
(mk F v hv) (mk F w hw) = mk F v…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`：mk_eq_mk_iff_crossPr
oduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : mk F v hv = mk F 
w hw ↔ crossProduct v w = 0
-/
lemma cross_self (v : ℙ F (Fin 3 → F)) : cross v v = v := by
  induction v with | h v hv =>
  rw [cross_mk_of_cross_eq_zero]
  rw [← mk_eq_mk_iff_crossProduct_eq_zero hv]
/-
**Projectivization.cross_mk_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：cross_mk_of_ne {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (h : mk F v 
hv != mk F w hw) : cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w) (mt (
mk_eq_mk_iff_crossProduct_eq_zero hv hw).mpr h)
参数：hv : v != 0；hw : w != 0；h : mk F v hv != mk F w hw。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`：mk_eq_mk_iff_crossPr
oduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : mk F v hv = mk F 
w hw ↔ crossProduct v w = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk_of_cross_ne_zero`：cross_mk_of_cross_ne_zero {v
 w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) (h : crossProduct v w != 0) : cross
 (mk F v hv) (mk F w hw) = mk F …
-/
lemma cross_mk_of_ne {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) (h : mk F v hv ≠ mk F w hw) :
    cross (mk F v hv) (mk F w hw) = mk F (crossProduct v w)
      (mt (mk_eq_mk_iff_crossProduct_eq_zero hv hw).mpr h) := by
  rw [cross_mk_of_cross_ne_zero]
/-
**Projectivization.cross_comm** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：cross_comm (v w : ℙ F (Fin 3 -> F)) : cross v w = cross w v
参数：v w : ℙ F (Fin 3 -> F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`：mk_eq_mk_iff_crossPr
oduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : mk F v hv = mk F 
w hw ↔ crossProduct v w = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk_of_ne`：cross_mk_of_ne {v w : Fin 3 -> F} (hv :
 v != 0) (hw : w != 0) (h : mk F v hv != mk F w hw) : cross (mk F v hv) (mk F w 
hw) = mk F (crossProd…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cross_anticomm`：cross_anticomm (v w : Fin 3 -> R) : -(v ⨯₃ w) = w ⨯₃ v
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `cross_self`：cross_self (v : Fin 3 -> R) : v ⨯₃ v = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma cross_comm (v w : ℙ F (Fin 3 → F)) : cross v w = cross w v := by
  rcases eq_or_ne v w with rfl | h
  · rfl
  · induction v with | h v hv =>
    induction w with | h w hw =>
    rw [cross_mk_of_ne hv hw h, cross_mk_of_ne hw hv h.symm, mk_eq_mk_iff_crossProduct_eq_zero,
      ← cross_anticomm v w, map_neg, _root_.cross_self, neg_zero]
/-
**Projectivization.cross_orthogonal_left** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviza
tion`。
形式化陈述：cross_orthogonal_left {v w : ℙ F (Fin 3 -> F)} (h : v != w) : (cross v w).
orthogonal v
参数：Fin 3 -> F；h : v != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`：mk_eq_mk_iff_crossPr
oduct_eq_zero {v w : Fin 3 -> F} (hv : v != 0) (hw : w != 0) : mk F v hv = mk F 
w hw ↔ crossProduct v w = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_mk_of_ne`：cross_mk_of_ne {v w : Fin 3 -> F} (hv :
 v != 0) (hw : w != 0) (h : mk F v hv != mk F w hw) : cross (mk F v hv) (mk F w 
hw) = mk F (crossProd…
· 使用引理 `Projectivization.orthogonal_mk`：orthogonal_mk {v w : m -> F} (hv : v != 
0) (hw : w != 0) : orthogonal (mk F v hv) (mk F w hw) ↔ v ⬝ᵥ w = 0
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `dot_self_cross`：dot_self_cross (v w : Fin 3 -> R) : v ⬝ᵥ v ⨯₃ w = 0
-/
theorem cross_orthogonal_left {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    (cross v w).orthogonal v := by
  induction v with | h v hv =>
  induction w with | h w hw =>
  rw [cross_mk_of_ne hv hw h, orthogonal_mk, dotProduct_comm, dot_self_cross]
/-
**Projectivization.cross_orthogonal_right** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviz
ation`。
形式化陈述：cross_orthogonal_right {v w : ℙ F (Fin 3 -> F)} (h : v != w) : (cross v w)
.orthogonal w
参数：Fin 3 -> F；h : v != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.cross_comm`：cross_comm (v w : ℙ F (Fin 3 -> F)) : cross
 v w = cross w v
· 使用定理 `Projectivization.cross_orthogonal_left`：cross_orthogonal_left {v w : ℙ F
 (Fin 3 -> F)} (h : v != w) : (cross v w).orthogonal v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem cross_orthogonal_right {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    (cross v w).orthogonal w := by
  rw [cross_comm]
  exact cross_orthogonal_left h.symm
/-
**Projectivization.orthogonal_cross_left** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviza
tion`。
形式化陈述：orthogonal_cross_left {v w : ℙ F (Fin 3 -> F)} (h : v != w) : v.orthogonal
 (cross v w)
参数：Fin 3 -> F；h : v != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.orthogonal_comm`：orthogonal_comm {v w : ℙ F (m -> F)} :
 orthogonal v w ↔ orthogonal w v
· 使用定理 `Projectivization.cross_orthogonal_left`：cross_orthogonal_left {v w : ℙ F
 (Fin 3 -> F)} (h : v != w) : (cross v w).orthogonal v
-/
theorem orthogonal_cross_left {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    v.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_left h
/-
**Projectivization.orthogonal_cross_right** 是 Mathlib 中的一个引理，位于命名空间 `Projectiviz
ation`。
形式化陈述：orthogonal_cross_right {v w : ℙ F (Fin 3 -> F)} (h : v != w) : w.orthogona
l (cross v w)
参数：Fin 3 -> F；h : v != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.orthogonal_comm`：orthogonal_comm {v w : ℙ F (m -> F)} :
 orthogonal v w ↔ orthogonal w v
· 使用定理 `Projectivization.cross_orthogonal_right`：cross_orthogonal_right {v w : ℙ
 F (Fin 3 -> F)} (h : v != w) : (cross v w).orthogonal w
-/
lemma orthogonal_cross_right {v w : ℙ F (Fin 3 → F)} (h : v ≠ w) :
    w.orthogonal (cross v w) := by
  rw [orthogonal_comm]
  exact cross_orthogonal_right h

end CrossProduct

end Projectivization

