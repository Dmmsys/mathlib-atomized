/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion

/-!
# Dual quaternions

Similar to the way that rotations in 3D space can be represented by quaternions of unit length,
rigid motions in 3D space can be represented by dual quaternions of unit length.

## Main results

* `Quaternion.dualNumberEquiv`: quaternions over dual numbers or dual
  numbers over quaternions are equivalent constructions.

## References

* <https://en.wikipedia.org/wiki/Dual_quaternion>
-/

@[expose] public section


variable {R : Type*} [CommRing R]

namespace Quaternion

set_option backward.isDefEq.respectTransparency.types false in
/-- The dual quaternions can be equivalently represented as a quaternion with dual coefficients,
or as a dual number with quaternion coefficients.

See also `Matrix.dualNumberEquiv` for a similar result. -/
/-
**Quaternion.dualNumberEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：dualNumberEquiv : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R
) where toFun q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual quaternions can be equivalently represented as a quaternion with dual c
oefficients,
or as a dual number with quaternion coefficients.

See also `Matrix.dualNumberEquiv` for a similar result.
-/
def dualNumberEquiv : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  toFun q :=
    (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  map_mul' := by
    intros
    ext : 1
    · rfl
    · dsimp
      congr 1 <;> simp <;> ring
  map_add' := by
    intros
    rfl
  commutes' _ := rfl

/-! Lemmas characterizing `Quaternion.dualNumberEquiv`. -/


-- `simps` can't work on `DualNumber` because it's not a structure
@[simp]
/-
**Quaternion.re_fst_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv 
q).fst.re = q.re.fst
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.re = q.re.fst :=
  rfl

@[simp]
/-
**Quaternion.imI_fst_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).fst.imI = q.imI.fst
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imI = q.imI.fst :=
  rfl

@[simp]
/-
**Quaternion.imJ_fst_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).fst.imJ = q.imJ.fst
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imJ = q.imJ.fst :=
  rfl

@[simp]
/-
**Quaternion.imK_fst_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).fst.imK = q.imK.fst
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imK = q.imK.fst :=
  rfl

@[simp]
/-
**Quaternion.re_snd_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv 
q).snd.re = q.re.snd
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.re = q.re.snd :=
  rfl

@[simp]
/-
**Quaternion.imI_snd_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).snd.imI = q.imI.snd
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imI = q.imI.snd :=
  rfl

@[simp]
/-
**Quaternion.imJ_snd_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).snd.imJ = q.imJ.snd
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imJ = q.imJ.snd :=
  rfl

@[simp]
/-
**Quaternion.imK_snd_dualNumberEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) : (dualNumberEquiv
 q).snd.imK = q.imK.snd
参数：q : Quaternion (DualNumber R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imK = q.imK.snd :=
  rfl

@[simp]
/-
**Quaternion.fst_re_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumberE
quiv.symm d).re.fst = d.fst.re
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.fst = d.fst.re :=
  rfl

@[simp]
/-
**Quaternion.fst_imI_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imI.fst = d.fst.imI
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.fst = d.fst.imI :=
  rfl

@[simp]
/-
**Quaternion.fst_imJ_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imJ.fst = d.fst.imJ
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.fst = d.fst.imJ :=
  rfl

@[simp]
/-
**Quaternion.fst_imK_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imK.fst = d.fst.imK
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.fst = d.fst.imK :=
  rfl

@[simp]
/-
**Quaternion.snd_re_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumberE
quiv.symm d).re.snd = d.snd.re
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.snd = d.snd.re :=
  rfl

@[simp]
/-
**Quaternion.snd_imI_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imI.snd = d.snd.imI
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.snd = d.snd.imI :=
  rfl

@[simp]
/-
**Quaternion.snd_imJ_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imJ.snd = d.snd.imJ
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.snd = d.snd.imJ :=
  rfl

@[simp]
/-
**Quaternion.snd_imK_dualNumberEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`
。
形式化陈述：snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) : (dualNumber
Equiv.symm d).imK.snd = d.snd.imK
参数：d : DualNumber (Quaternion R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.snd = d.snd.imK :=
  rfl

end Quaternion

