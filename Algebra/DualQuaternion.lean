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
/--
Definition of `dualNumberEquiv` / `dualNumberEquiv` 的定义

English:
definition dualNumberEquiv
  signature: : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  body: (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  map_mul' := by
    intros
    ext : 1
    · rfl
    · dsimp
      congr 1 <;> simp <;> ring
  

中文:
定义 dualNumberEquiv
  签名: : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  定义体: (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  map_mul' := by
    intros
    ext : 1
    · rfl
    · dsimp
      congr 1 <;> simp <;> ring
  

Depends on / 依赖: commutes, d.fst.imI, d.fst.imJ, d.fst.imK, d.fst.re, d.snd.imI, d.snd.imJ, d.snd.imK, d.snd.re, intros, invFun, map_add, map_mul, q.imI.fst, q.imI.snd, q.imJ.fst, q.imJ.snd, q.imK.fst, q.imK.snd, q.re.fst
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
/--
theorem `re_fst_dualNumberEquiv` / 定理 `re_fst_dualNumberEquiv`

English:
theorem re_fst_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 re_fst_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.re = q.re.fst :=
  rfl

@[simp]
/--
theorem `imI_fst_dualNumberEquiv` / 定理 `imI_fst_dualNumberEquiv`

English:
theorem imI_fst_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imI_fst_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imI = q.imI.fst :=
  rfl

@[simp]
/--
theorem `imJ_fst_dualNumberEquiv` / 定理 `imJ_fst_dualNumberEquiv`

English:
theorem imJ_fst_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imJ_fst_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imJ = q.imJ.fst :=
  rfl

@[simp]
/--
theorem `imK_fst_dualNumberEquiv` / 定理 `imK_fst_dualNumberEquiv`

English:
theorem imK_fst_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imK_fst_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imK = q.imK.fst :=
  rfl

@[simp]
/--
theorem `re_snd_dualNumberEquiv` / 定理 `re_snd_dualNumberEquiv`

English:
theorem re_snd_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 re_snd_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.re = q.re.snd :=
  rfl

@[simp]
/--
theorem `imI_snd_dualNumberEquiv` / 定理 `imI_snd_dualNumberEquiv`

English:
theorem imI_snd_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imI_snd_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imI = q.imI.snd :=
  rfl

@[simp]
/--
theorem `imJ_snd_dualNumberEquiv` / 定理 `imJ_snd_dualNumberEquiv`

English:
theorem imJ_snd_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imJ_snd_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imJ = q.imJ.snd :=
  rfl

@[simp]
/--
theorem `imK_snd_dualNumberEquiv` / 定理 `imK_snd_dualNumberEquiv`

English:
theorem imK_snd_dualNumberEquiv
  given: (q : Quaternion (DualNumber R))
  proof: rfl

@[simp]

中文:
定理 imK_snd_dualNumberEquiv
  条件: (q : Quaternion (DualNumber R))
  证明: rfl

@[simp]
-/
theorem imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imK = q.imK.snd :=
  rfl

@[simp]
/--
theorem `fst_re_dualNumberEquiv_symm` / 定理 `fst_re_dualNumberEquiv_symm`

English:
theorem fst_re_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 fst_re_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.fst = d.fst.re :=
  rfl

@[simp]
/--
theorem `fst_imI_dualNumberEquiv_symm` / 定理 `fst_imI_dualNumberEquiv_symm`

English:
theorem fst_imI_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 fst_imI_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.fst = d.fst.imI :=
  rfl

@[simp]
/--
theorem `fst_imJ_dualNumberEquiv_symm` / 定理 `fst_imJ_dualNumberEquiv_symm`

English:
theorem fst_imJ_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 fst_imJ_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.fst = d.fst.imJ :=
  rfl

@[simp]
/--
theorem `fst_imK_dualNumberEquiv_symm` / 定理 `fst_imK_dualNumberEquiv_symm`

English:
theorem fst_imK_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 fst_imK_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.fst = d.fst.imK :=
  rfl

@[simp]
/--
theorem `snd_re_dualNumberEquiv_symm` / 定理 `snd_re_dualNumberEquiv_symm`

English:
theorem snd_re_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 snd_re_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.snd = d.snd.re :=
  rfl

@[simp]
/--
theorem `snd_imI_dualNumberEquiv_symm` / 定理 `snd_imI_dualNumberEquiv_symm`

English:
theorem snd_imI_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 snd_imI_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.snd = d.snd.imI :=
  rfl

@[simp]
/--
theorem `snd_imJ_dualNumberEquiv_symm` / 定理 `snd_imJ_dualNumberEquiv_symm`

English:
theorem snd_imJ_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

@[simp]

中文:
定理 snd_imJ_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl

@[simp]
-/
theorem snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.snd = d.snd.imJ :=
  rfl

@[simp]
/--
theorem `snd_imK_dualNumberEquiv_symm` / 定理 `snd_imK_dualNumberEquiv_symm`

English:
theorem snd_imK_dualNumberEquiv_symm
  given: (d : DualNumber (Quaternion R))
  proof: rfl

中文:
定理 snd_imK_dualNumberEquiv_symm
  条件: (d : DualNumber (Quaternion R))
  证明: rfl
-/
theorem snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.snd = d.snd.imK :=
  rfl

end Quaternion
