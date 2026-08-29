/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Fin

/-!
# Finite intervals in `Fin n`

This file proves that `Fin n` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as Finsets and Fintypes.
-/

public section

assert_not_exists MonoidWithZero

open Finset Function

namespace Fin

variable (n : Nat)


/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: (n : Nat)
  body: attachFin (Icc a b) fun x hx => (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx => (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx => (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx => (mem_Ioo.mp hx).2.trans b

中文:
实例 instLocallyFiniteOrder
  签名: (n : 自然数)
  定义体: attachFin (Icc a b) fun x hx => (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx => (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx => (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx => (mem_Ioo.mp hx).2.trans b

Depends on / 依赖: attachFin, mem_Icc, mem_Icc.mp, trans_lt
-/
instance instLocallyFiniteOrder (n : Nat) : LocallyFiniteOrder (Fin n) where
  finsetIcc a b := attachFin (Icc a b) fun x hx => (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx => (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx => (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx => (mem_Ioo.mp hx).2.trans b.2
  finset_mem_Icc a b := by simp
  finset_mem_Ico a b := by simp
  finset_mem_Ioc a b := by simp
  finset_mem_Ioo a b := by simp

/--
Instance `instLocallyFiniteOrderBot` / 实例 `instLocallyFiniteOrderBot`

English:
instance instLocallyFiniteOrderBot
  signature: : forall n, LocallyFiniteOrderBot (Fin n)

中文:
实例 instLocallyFiniteOrderBot
  签名: : 对任意 n, LocallyFiniteOrderBot (Fin n)
-/
instance instLocallyFiniteOrderBot : forall n, LocallyFiniteOrderBot (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderBot
  | _ + 1 => inferInstance

/--
Instance `instLocallyFiniteOrderTop` / 实例 `instLocallyFiniteOrderTop`

English:
instance instLocallyFiniteOrderTop
  signature: : forall n, LocallyFiniteOrderTop (Fin n)

中文:
实例 instLocallyFiniteOrderTop
  签名: : 对任意 n, LocallyFiniteOrderTop (Fin n)
-/
instance instLocallyFiniteOrderTop : forall n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

variable {n}
variable {m : Nat} (a b : Fin n)

@[simp]
/--
theorem `attachFin_Icc` / 定理 `attachFin_Icc`

English:
theorem attachFin_Icc
  proof: rfl

@[simp]

中文:
定理 attachFin_Icc
  证明: rfl

@[simp]
-/
theorem attachFin_Icc :
    attachFin (Icc a b) (fun _x hx => (mem_Icc.mp hx).2.trans_lt b.2) = Icc a b :=
  rfl

@[simp]
/--
theorem `attachFin_Ico` / 定理 `attachFin_Ico`

English:
theorem attachFin_Ico
  proof: rfl

@[simp]

中文:
定理 attachFin_Ico
  证明: rfl

@[simp]
-/
theorem attachFin_Ico :
    attachFin (Ico a b) (fun _x hx => (mem_Ico.mp hx).2.trans b.2) = Ico a b :=
  rfl

@[simp]
/--
theorem `attachFin_Ioc` / 定理 `attachFin_Ioc`

English:
theorem attachFin_Ioc
  proof: rfl

@[simp]

中文:
定理 attachFin_Ioc
  证明: rfl

@[simp]
-/
theorem attachFin_Ioc :
    attachFin (Ioc a b) (fun _x hx => (mem_Ioc.mp hx).2.trans_lt b.2) = Ioc a b :=
  rfl

@[simp]
/--
theorem `attachFin_Ioo` / 定理 `attachFin_Ioo`

English:
theorem attachFin_Ioo
  proof: rfl

@[simp]

中文:
定理 attachFin_Ioo
  证明: rfl

@[simp]
-/
theorem attachFin_Ioo :
    attachFin (Ioo a b) (fun _x hx => (mem_Ioo.mp hx).2.trans b.2) = Ioo a b :=
  rfl

@[simp]
/--
theorem `attachFin_uIcc` / 定理 `attachFin_uIcc`

English:
theorem attachFin_uIcc
  proof: rfl

@[simp]

中文:
定理 attachFin_uIcc
  证明: rfl

@[simp]
-/
theorem attachFin_uIcc :
    attachFin (uIcc a b) (fun _x hx => (mem_Icc.mp hx).2.trans_lt (max a b).2) = uIcc a b :=
  rfl

@[simp]
/--
theorem `attachFin_Ico_eq_Ici` / 定理 `attachFin_Ico_eq_Ici`

English:
theorem attachFin_Ico_eq_Ici
  statement: attachFin (Ico a n) (fun _x hx => (mem_Ico.mp hx).2) = Ici a
  proof: by
  ext; simp

@[simp]

中文:
定理 attachFin_Ico_eq_Ici
  结论: attachFin (Ico a n) (fun _x hx => (mem_Ico.mp hx).2) = Ici a
  证明: by
  ext; simp

@[simp]
-/
theorem attachFin_Ico_eq_Ici : attachFin (Ico a n) (fun _x hx => (mem_Ico.mp hx).2) = Ici a := by
  ext; simp

@[simp]
/--
theorem `attachFin_Ioo_eq_Ioi` / 定理 `attachFin_Ioo_eq_Ioi`

English:
theorem attachFin_Ioo_eq_Ioi
  statement: attachFin (Ioo a n) (fun _x hx => (mem_Ioo.mp hx).2) = Ioi a
  proof: by
  ext; simp

@[simp]

中文:
定理 attachFin_Ioo_eq_Ioi
  结论: attachFin (Ioo a n) (fun _x hx => (mem_Ioo.mp hx).2) = Ioi a
  证明: by
  ext; simp

@[simp]
-/
theorem attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fun _x hx => (mem_Ioo.mp hx).2) = Ioi a := by
  ext; simp

@[simp]
/--
theorem `attachFin_Iic` / 定理 `attachFin_Iic`

English:
theorem attachFin_Iic
  statement: attachFin (Iic a) (fun _x hx => (mem_Iic.mp hx).trans_lt a.2) = Iic a
  proof: by
  ext; simp

@[simp]

中文:
定理 attachFin_Iic
  结论: attachFin (Iic a) (fun _x hx => (mem_Iic.mp hx).trans_lt a.2) = Iic a
  证明: by
  ext; simp

@[simp]
-/
theorem attachFin_Iic : attachFin (Iic a) (fun _x hx => (mem_Iic.mp hx).trans_lt a.2) = Iic a := by
  ext; simp

@[simp]
/--
theorem `attachFin_Iio` / 定理 `attachFin_Iio`

English:
theorem attachFin_Iio
  statement: attachFin (Iio a) (fun _x hx => (mem_Iio.mp hx).trans a.2) = Iio a
  proof: by
  ext; simp

中文:
定理 attachFin_Iio
  结论: attachFin (Iio a) (fun _x hx => (mem_Iio.mp hx).trans a.2) = Iio a
  证明: by
  ext; simp
-/
theorem attachFin_Iio : attachFin (Iio a) (fun _x hx => (mem_Iio.mp hx).trans a.2) = Iio a := by
  ext; simp

section val

/-!
### Images under `Fin.val`
-/

@[simp]
/--
theorem `finsetImage_val_Icc` / 定理 `finsetImage_val_Icc`

English:
theorem finsetImage_val_Icc
  statement: (Icc a b).image val = Icc (a : Nat) b
  proof: image_val_attachFin _

@[simp]

中文:
定理 finsetImage_val_Icc
  结论: (Icc a b).image val = Icc (a : 自然数) b
  证明: image_val_attachFin _

@[simp]

Depends on / 依赖: image_val_attachFin
-/
theorem finsetImage_val_Icc : (Icc a b).image val = Icc (a : Nat) b :=
  image_val_attachFin _

@[simp]
/--
theorem `finsetImage_val_Ico` / 定理 `finsetImage_val_Ico`

English:
theorem finsetImage_val_Ico
  statement: (Ico a b).image val = Ico (a : Nat) b
  proof: image_val_attachFin _

@[simp]

中文:
定理 finsetImage_val_Ico
  结论: (Ico a b).image val = Ico (a : 自然数) b
  证明: image_val_attachFin _

@[simp]

Depends on / 依赖: image_val_attachFin
-/
theorem finsetImage_val_Ico : (Ico a b).image val = Ico (a : Nat) b :=
  image_val_attachFin _

@[simp]
/--
theorem `finsetImage_val_Ioc` / 定理 `finsetImage_val_Ioc`

English:
theorem finsetImage_val_Ioc
  statement: (Ioc a b).image val = Ioc (a : Nat) b
  proof: image_val_attachFin _

@[simp]

中文:
定理 finsetImage_val_Ioc
  结论: (Ioc a b).image val = Ioc (a : 自然数) b
  证明: image_val_attachFin _

@[simp]

Depends on / 依赖: image_val_attachFin
-/
theorem finsetImage_val_Ioc : (Ioc a b).image val = Ioc (a : Nat) b :=
  image_val_attachFin _

@[simp]
/--
theorem `finsetImage_val_Ioo` / 定理 `finsetImage_val_Ioo`

English:
theorem finsetImage_val_Ioo
  statement: (Ioo a b).image val = Ioo (a : Nat) b
  proof: image_val_attachFin _

@[simp]

中文:
定理 finsetImage_val_Ioo
  结论: (Ioo a b).image val = Ioo (a : 自然数) b
  证明: image_val_attachFin _

@[simp]

Depends on / 依赖: image_val_attachFin
-/
theorem finsetImage_val_Ioo : (Ioo a b).image val = Ioo (a : Nat) b :=
  image_val_attachFin _

@[simp]
/--
theorem `finsetImage_val_uIcc` / 定理 `finsetImage_val_uIcc`

English:
theorem finsetImage_val_uIcc
  statement: (uIcc a b).image val = uIcc (a : Nat) b
  proof: finsetImage_val_Icc _ _

@[simp]

中文:
定理 finsetImage_val_uIcc
  结论: (uIcc a b).image val = uIcc (a : 自然数) b
  证明: finsetImage_val_Icc _ _

@[simp]

Depends on / 依赖: finsetImage_val_Icc
-/
theorem finsetImage_val_uIcc : (uIcc a b).image val = uIcc (a : Nat) b :=
  finsetImage_val_Icc _ _

@[simp]
/--
theorem `finsetImage_val_Ici` / 定理 `finsetImage_val_Ici`

English:
theorem finsetImage_val_Ici
  statement: (Ici a).image val = Ico (a : Nat) n
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_val_Ici
  结论: (Ici a).image val = Ico (a : 自然数) n
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_val_Ici : (Ici a).image val = Ico (a : Nat) n := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_val_Ioi` / 定理 `finsetImage_val_Ioi`

English:
theorem finsetImage_val_Ioi
  statement: (Ioi a).image val = Ioo (a : Nat) n
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_val_Ioi
  结论: (Ioi a).image val = Ioo (a : 自然数) n
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_val_Ioi : (Ioi a).image val = Ioo (a : Nat) n := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_val_Iic` / 定理 `finsetImage_val_Iic`

English:
theorem finsetImage_val_Iic
  statement: (Iic a).image val = Iic (a : Nat)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_val_Iic
  结论: (Iic a).image val = Iic (a : 自然数)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_val_Iic : (Iic a).image val = Iic (a : Nat) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_val_Iio` / 定理 `finsetImage_val_Iio`

English:
theorem finsetImage_val_Iio
  statement: (Iio b).image val = Iio (b : Nat)
  proof: by simp [← coe_inj]

中文:
定理 finsetImage_val_Iio
  结论: (Iio b).image val = Iio (b : 自然数)
  证明: by simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_val_Iio : (Iio b).image val = Iio (b : Nat) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.valEmbedding`
-/

@[simp]
/--
theorem `map_valEmbedding_Icc` / 定理 `map_valEmbedding_Icc`

English:
theorem map_valEmbedding_Icc
  statement: (Icc a b).map Fin.valEmbedding = Icc (a : Nat) b
  proof: map_valEmbedding_attachFin _

@[simp]

中文:
定理 map_valEmbedding_Icc
  结论: (Icc a b).map Fin.valEmbedding = Icc (a : 自然数) b
  证明: map_valEmbedding_attachFin _

@[simp]

Depends on / 依赖: map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc (a : Nat) b :=
  map_valEmbedding_attachFin _

@[simp]
/--
theorem `map_valEmbedding_Ico` / 定理 `map_valEmbedding_Ico`

English:
theorem map_valEmbedding_Ico
  statement: (Ico a b).map Fin.valEmbedding = Ico (a : Nat) b
  proof: map_valEmbedding_attachFin _

@[simp]

中文:
定理 map_valEmbedding_Ico
  结论: (Ico a b).map Fin.valEmbedding = Ico (a : 自然数) b
  证明: map_valEmbedding_attachFin _

@[simp]

Depends on / 依赖: Submodule, Submodule.module, map_valEmbedding_attachFin, module
-/
theorem map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico (a : Nat) b :=
  map_valEmbedding_attachFin _

@[simp]
/--
theorem `map_valEmbedding_Ioc` / 定理 `map_valEmbedding_Ioc`

English:
theorem map_valEmbedding_Ioc
  statement: (Ioc a b).map Fin.valEmbedding = Ioc (a : Nat) b
  proof: map_valEmbedding_attachFin _

@[simp]

中文:
定理 map_valEmbedding_Ioc
  结论: (Ioc a b).map Fin.valEmbedding = Ioc (a : 自然数) b
  证明: map_valEmbedding_attachFin _

@[simp]

Depends on / 依赖: map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc (a : Nat) b :=
  map_valEmbedding_attachFin _

@[simp]
/--
theorem `map_valEmbedding_Ioo` / 定理 `map_valEmbedding_Ioo`

English:
theorem map_valEmbedding_Ioo
  statement: (Ioo a b).map Fin.valEmbedding = Ioo (a : Nat) b
  proof: map_valEmbedding_attachFin _

@[simp]

中文:
定理 map_valEmbedding_Ioo
  结论: (Ioo a b).map Fin.valEmbedding = Ioo (a : 自然数) b
  证明: map_valEmbedding_attachFin _

@[simp]

Depends on / 依赖: map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo (a : Nat) b :=
  map_valEmbedding_attachFin _

@[simp]
/--
theorem `map_valEmbedding_uIcc` / 定理 `map_valEmbedding_uIcc`

English:
theorem map_valEmbedding_uIcc
  statement: (uIcc a b).map valEmbedding = uIcc (a : Nat) b
  proof: map_valEmbedding_Icc _ _

@[simp]

中文:
定理 map_valEmbedding_uIcc
  结论: (uIcc a b).map valEmbedding = uIcc (a : 自然数) b
  证明: map_valEmbedding_Icc _ _

@[simp]

Depends on / 依赖: map_valEmbedding_Icc
-/
theorem map_valEmbedding_uIcc : (uIcc a b).map valEmbedding = uIcc (a : Nat) b :=
  map_valEmbedding_Icc _ _

@[simp]
/--
theorem `map_valEmbedding_Ici` / 定理 `map_valEmbedding_Ici`

English:
theorem map_valEmbedding_Ici
  statement: (Ici a).map Fin.valEmbedding = Ico (a : Nat) n
  proof: by
  rw [← attachFin_Ico_eq_Ici]; rw [map_valEmbedding_attachFin]

@[simp]

中文:
定理 map_valEmbedding_Ici
  结论: (Ici a).map Fin.valEmbedding = Ico (a : 自然数) n
  证明: by
  rw [← attachFin_Ico_eq_Ici]; rw [map_valEmbedding_attachFin]

@[simp]

Depends on / 依赖: attachFin_Ico_eq_Ici, map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Ico (a : Nat) n := by
  rw [← attachFin_Ico_eq_Ici]; rw [map_valEmbedding_attachFin]

@[simp]
/--
theorem `map_valEmbedding_Ioi` / 定理 `map_valEmbedding_Ioi`

English:
theorem map_valEmbedding_Ioi
  statement: (Ioi a).map Fin.valEmbedding = Ioo (a : Nat) n
  proof: by
  rw [← attachFin_Ioo_eq_Ioi]; rw [map_valEmbedding_attachFin]

@[simp]

中文:
定理 map_valEmbedding_Ioi
  结论: (Ioi a).map Fin.valEmbedding = Ioo (a : 自然数) n
  证明: by
  rw [← attachFin_Ioo_eq_Ioi]; rw [map_valEmbedding_attachFin]

@[simp]

Depends on / 依赖: attachFin_Ioo_eq_Ioi, map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioo (a : Nat) n := by
  rw [← attachFin_Ioo_eq_Ioi]; rw [map_valEmbedding_attachFin]

@[simp]
/--
theorem `map_valEmbedding_Iic` / 定理 `map_valEmbedding_Iic`

English:
theorem map_valEmbedding_Iic
  statement: (Iic a).map Fin.valEmbedding = Iic (a : Nat)
  proof: by
  rw [← attachFin_Iic]; rw [map_valEmbedding_attachFin]

@[simp]

中文:
定理 map_valEmbedding_Iic
  结论: (Iic a).map Fin.valEmbedding = Iic (a : 自然数)
  证明: by
  rw [← attachFin_Iic]; rw [map_valEmbedding_attachFin]

@[simp]

Depends on / 依赖: attachFin_Iic, map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Iic : (Iic a).map Fin.valEmbedding = Iic (a : Nat) := by
  rw [← attachFin_Iic]; rw [map_valEmbedding_attachFin]

@[simp]
/--
theorem `map_valEmbedding_Iio` / 定理 `map_valEmbedding_Iio`

English:
theorem map_valEmbedding_Iio
  statement: (Iio a).map Fin.valEmbedding = Iio (a : Nat)
  proof: by
  rw [← attachFin_Iio]; rw [map_valEmbedding_attachFin]

中文:
定理 map_valEmbedding_Iio
  结论: (Iio a).map Fin.valEmbedding = Iio (a : 自然数)
  证明: by
  rw [← attachFin_Iio]; rw [map_valEmbedding_attachFin]

Depends on / 依赖: attachFin_Iio, map_valEmbedding_attachFin
-/
theorem map_valEmbedding_Iio : (Iio a).map Fin.valEmbedding = Iio (a : Nat) := by
  rw [← attachFin_Iio]; rw [map_valEmbedding_attachFin]

end val

section castLE

/-!
### Image under `Fin.castLE`
-/

@[simp]
/--
theorem `finsetImage_castLE_Icc` / 定理 `finsetImage_castLE_Icc`

English:
theorem finsetImage_castLE_Icc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_Icc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Icc (h : n <= m) :
    (Icc a b).image (castLE h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_Ico` / 定理 `finsetImage_castLE_Ico`

English:
theorem finsetImage_castLE_Ico
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_Ico
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Ico (h : n <= m) :
    (Ico a b).image (castLE h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_Ioc` / 定理 `finsetImage_castLE_Ioc`

English:
theorem finsetImage_castLE_Ioc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_Ioc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Ioc (h : n <= m) :
    (Ioc a b).image (castLE h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_Ioo` / 定理 `finsetImage_castLE_Ioo`

English:
theorem finsetImage_castLE_Ioo
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_Ioo
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Ioo (h : n <= m) :
    (Ioo a b).image (castLE h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_uIcc` / 定理 `finsetImage_castLE_uIcc`

English:
theorem finsetImage_castLE_uIcc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_uIcc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_uIcc (h : n <= m) :
    (uIcc a b).image (castLE h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_Iic` / 定理 `finsetImage_castLE_Iic`

English:
theorem finsetImage_castLE_Iic
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castLE_Iic
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Iic (h : n <= m) :
    (Iic a).image (castLE h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castLE_Iio` / 定理 `finsetImage_castLE_Iio`

English:
theorem finsetImage_castLE_Iio
  given: (h : n <= m)
  proof: by simp [← coe_inj]

中文:
定理 finsetImage_castLE_Iio
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castLE_Iio (h : n <= m) :
    (Iio a).image (castLE h) = Iio (castLE h a) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.castLEEmb`
-/

@[simp]
/--
theorem `map_castLEEmb_Icc` / 定理 `map_castLEEmb_Icc`

English:
theorem map_castLEEmb_Icc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_Icc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Icc (h : n <= m) :
    (Icc a b).map (castLEEmb h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_Ico` / 定理 `map_castLEEmb_Ico`

English:
theorem map_castLEEmb_Ico
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_Ico
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Ico (h : n <= m) :
    (Ico a b).map (castLEEmb h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_Ioc` / 定理 `map_castLEEmb_Ioc`

English:
theorem map_castLEEmb_Ioc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_Ioc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Ioc (h : n <= m) :
    (Ioc a b).map (castLEEmb h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_Ioo` / 定理 `map_castLEEmb_Ioo`

English:
theorem map_castLEEmb_Ioo
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_Ioo
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Ioo (h : n <= m) :
    (Ioo a b).map (castLEEmb h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_uIcc` / 定理 `map_castLEEmb_uIcc`

English:
theorem map_castLEEmb_uIcc
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_uIcc
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_uIcc (h : n <= m) :
    (uIcc a b).map (castLEEmb h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_Iic` / 定理 `map_castLEEmb_Iic`

English:
theorem map_castLEEmb_Iic
  given: (h : n <= m)
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 map_castLEEmb_Iic
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Iic (h : n <= m) :
    (Iic a).map (castLEEmb h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
/--
theorem `map_castLEEmb_Iio` / 定理 `map_castLEEmb_Iio`

English:
theorem map_castLEEmb_Iio
  given: (h : n <= m)
  proof: by simp [← coe_inj]

中文:
定理 map_castLEEmb_Iio
  条件: (h : n <= m)
  证明: by simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_castLEEmb_Iio (h : n <= m) :
    (Iio a).map (castLEEmb h) = Iio (castLE h a) := by simp [← coe_inj]

end castLE

section castAdd

/-!
### Images under `Fin.castAdd`
-/

@[simp]
/--
theorem `finsetImage_castAdd_Icc` / 定理 `finsetImage_castAdd_Icc`

English:
theorem finsetImage_castAdd_Icc
  given: (m) (i j : Fin n)
  proof: finsetImage_castLE_Icc ..

@[simp]

中文:
定理 finsetImage_castAdd_Icc
  条件: (m) (i j : Fin n)
  证明: finsetImage_castLE_Icc ..

@[simp]

Depends on / 依赖: finsetImage_castLE_Icc
-/
theorem finsetImage_castAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (castAdd m) = Icc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Icc ..

@[simp]
/--
theorem `finsetImage_castAdd_Ico` / 定理 `finsetImage_castAdd_Ico`

English:
theorem finsetImage_castAdd_Ico
  given: (m) (i j : Fin n)
  proof: finsetImage_castLE_Ico ..

@[simp]

中文:
定理 finsetImage_castAdd_Ico
  条件: (m) (i j : Fin n)
  证明: finsetImage_castLE_Ico ..

@[simp]

Depends on / 依赖: finsetImage_castLE_Ico
-/
theorem finsetImage_castAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (castAdd m) = Ico (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ico ..

@[simp]
/--
theorem `finsetImage_castAdd_Ioc` / 定理 `finsetImage_castAdd_Ioc`

English:
theorem finsetImage_castAdd_Ioc
  given: (m) (i j : Fin n)
  proof: finsetImage_castLE_Ioc ..

@[simp]

中文:
定理 finsetImage_castAdd_Ioc
  条件: (m) (i j : Fin n)
  证明: finsetImage_castLE_Ioc ..

@[simp]

Depends on / 依赖: finsetImage_castLE_Ioc
-/
theorem finsetImage_castAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (castAdd m) = Ioc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioc ..

@[simp]
/--
theorem `finsetImage_castAdd_Ioo` / 定理 `finsetImage_castAdd_Ioo`

English:
theorem finsetImage_castAdd_Ioo
  given: (m) (i j : Fin n)
  proof: finsetImage_castLE_Ioo ..

@[simp]

中文:
定理 finsetImage_castAdd_Ioo
  条件: (m) (i j : Fin n)
  证明: finsetImage_castLE_Ioo ..

@[simp]

Depends on / 依赖: finsetImage_castLE_Ioo
-/
theorem finsetImage_castAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (castAdd m) = Ioo (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioo ..

@[simp]
/--
theorem `finsetImage_castAdd_uIcc` / 定理 `finsetImage_castAdd_uIcc`

English:
theorem finsetImage_castAdd_uIcc
  given: (m) (i j : Fin n)
  proof: finsetImage_castLE_uIcc ..

@[simp]

中文:
定理 finsetImage_castAdd_uIcc
  条件: (m) (i j : Fin n)
  证明: finsetImage_castLE_uIcc ..

@[simp]

Depends on / 依赖: finsetImage_castLE_uIcc
-/
theorem finsetImage_castAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (castAdd m) = uIcc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_uIcc ..

@[simp]
/--
theorem `finsetImage_castAdd_Ici` / 定理 `finsetImage_castAdd_Ici`

English:
theorem finsetImage_castAdd_Ici
  given: (m) [NeZero m] (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castAdd_Ici
  条件: (m) [NeZero m] (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).image (castAdd m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castAdd_Ioi` / 定理 `finsetImage_castAdd_Ioi`

English:
theorem finsetImage_castAdd_Ioi
  given: (m) [NeZero m] (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_castAdd_Ioi
  条件: (m) [NeZero m] (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).image (castAdd m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_castAdd_Iic` / 定理 `finsetImage_castAdd_Iic`

English:
theorem finsetImage_castAdd_Iic
  given: (m) (i : Fin n)
  statement: (Iic i).image (castAdd m) = Iic (castAdd m i)
  proof: finsetImage_castLE_Iic i _

@[simp]

中文:
定理 finsetImage_castAdd_Iic
  条件: (m) (i : Fin n)
  结论: (Iic i).image (castAdd m) = Iic (castAdd m i)
  证明: finsetImage_castLE_Iic i _

@[simp]

Depends on / 依赖: finsetImage_castLE_Iic
-/
theorem finsetImage_castAdd_Iic (m) (i : Fin n) : (Iic i).image (castAdd m) = Iic (castAdd m i) :=
  finsetImage_castLE_Iic i _

@[simp]
/--
theorem `finsetImage_castAdd_Iio` / 定理 `finsetImage_castAdd_Iio`

English:
theorem finsetImage_castAdd_Iio
  given: (m) (i : Fin n)
  statement: (Iio i).image (castAdd m) = Iio (castAdd m i)
  proof: finsetImage_castLE_Iio ..

中文:
定理 finsetImage_castAdd_Iio
  条件: (m) (i : Fin n)
  结论: (Iio i).image (castAdd m) = Iio (castAdd m i)
  证明: finsetImage_castLE_Iio ..

Depends on / 依赖: finsetImage_castLE_Iio
-/
theorem finsetImage_castAdd_Iio (m) (i : Fin n) : (Iio i).image (castAdd m) = Iio (castAdd m i) :=
  finsetImage_castLE_Iio ..

/-!
### `Finset.map` along `Fin.castAddEmb`
-/

@[simp]
/--
theorem `map_castAddEmb_Icc` / 定理 `map_castAddEmb_Icc`

English:
theorem map_castAddEmb_Icc
  given: (m) (i j : Fin n)
  proof: map_castLEEmb_Icc ..

@[simp]

中文:
定理 map_castAddEmb_Icc
  条件: (m) (i j : Fin n)
  证明: map_castLEEmb_Icc ..

@[simp]

Depends on / 依赖: map_castLEEmb_Icc
-/
theorem map_castAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (castAddEmb m) = Icc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Icc ..

@[simp]
/--
theorem `map_castAddEmb_Ico` / 定理 `map_castAddEmb_Ico`

English:
theorem map_castAddEmb_Ico
  given: (m) (i j : Fin n)
  proof: map_castLEEmb_Ico ..

@[simp]

中文:
定理 map_castAddEmb_Ico
  条件: (m) (i j : Fin n)
  证明: map_castLEEmb_Ico ..

@[simp]

Depends on / 依赖: map_castLEEmb_Ico
-/
theorem map_castAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (castAddEmb m) = Ico (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ico ..

@[simp]
/--
theorem `map_castAddEmb_Ioc` / 定理 `map_castAddEmb_Ioc`

English:
theorem map_castAddEmb_Ioc
  given: (m) (i j : Fin n)
  proof: map_castLEEmb_Ioc ..

@[simp]

中文:
定理 map_castAddEmb_Ioc
  条件: (m) (i j : Fin n)
  证明: map_castLEEmb_Ioc ..

@[simp]

Depends on / 依赖: map_castLEEmb_Ioc
-/
theorem map_castAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (castAddEmb m) = Ioc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioc ..

@[simp]
/--
theorem `map_castAddEmb_Ioo` / 定理 `map_castAddEmb_Ioo`

English:
theorem map_castAddEmb_Ioo
  given: (m) (i j : Fin n)
  proof: map_castLEEmb_Ioo ..

@[simp]

中文:
定理 map_castAddEmb_Ioo
  条件: (m) (i j : Fin n)
  证明: map_castLEEmb_Ioo ..

@[simp]

Depends on / 依赖: map_castLEEmb_Ioo
-/
theorem map_castAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (castAddEmb m) = Ioo (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioo ..

@[simp]
/--
theorem `map_castAddEmb_uIcc` / 定理 `map_castAddEmb_uIcc`

English:
theorem map_castAddEmb_uIcc
  given: (m) (i j : Fin n)
  proof: map_castLEEmb_uIcc ..

@[simp]

中文:
定理 map_castAddEmb_uIcc
  条件: (m) (i j : Fin n)
  证明: map_castLEEmb_uIcc ..

@[simp]

Depends on / 依赖: map_castLEEmb_uIcc
-/
theorem map_castAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (castAddEmb m) = uIcc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_uIcc ..

@[simp]
/--
theorem `map_castAddEmb_Ici` / 定理 `map_castAddEmb_Ici`

English:
theorem map_castAddEmb_Ici
  given: (m) [NeZero m] (i : Fin n)
  proof: by
  simp [map_eq_image]

@[simp]

中文:
定理 map_castAddEmb_Ici
  条件: (m) [NeZero m] (i : Fin n)
  证明: by
  simp [map_eq_image]

@[simp]

Depends on / 依赖: map_eq_image
-/
theorem map_castAddEmb_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).map (castAddEmb m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [map_eq_image]

@[simp]
/--
theorem `map_castAddEmb_Ioi` / 定理 `map_castAddEmb_Ioi`

English:
theorem map_castAddEmb_Ioi
  given: (m) [NeZero m] (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 map_castAddEmb_Ioi
  条件: (m) [NeZero m] (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_castAddEmb_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).map (castAddEmb m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
/--
theorem `map_castAddEmb_Iic` / 定理 `map_castAddEmb_Iic`

English:
theorem map_castAddEmb_Iic
  given: (m) (i : Fin n)
  statement: (Iic i).map (castAddEmb m) = Iic (castAdd m i)
  proof: map_castLEEmb_Iic i _

@[simp]

中文:
定理 map_castAddEmb_Iic
  条件: (m) (i : Fin n)
  结论: (Iic i).map (castAddEmb m) = Iic (castAdd m i)
  证明: map_castLEEmb_Iic i _

@[simp]

Depends on / 依赖: map_castLEEmb_Iic
-/
theorem map_castAddEmb_Iic (m) (i : Fin n) : (Iic i).map (castAddEmb m) = Iic (castAdd m i) :=
  map_castLEEmb_Iic i _

@[simp]
/--
theorem `map_castAddEmb_Iio` / 定理 `map_castAddEmb_Iio`

English:
theorem map_castAddEmb_Iio
  given: (m) (i : Fin n)
  statement: (Iio i).map (castAddEmb m) = Iio (castAdd m i)
  proof: map_castLEEmb_Iio ..

中文:
定理 map_castAddEmb_Iio
  条件: (m) (i : Fin n)
  结论: (Iio i).map (castAddEmb m) = Iio (castAdd m i)
  证明: map_castLEEmb_Iio ..

Depends on / 依赖: map_castLEEmb_Iio
-/
theorem map_castAddEmb_Iio (m) (i : Fin n) : (Iio i).map (castAddEmb m) = Iio (castAdd m i) :=
  map_castLEEmb_Iio ..

end castAdd

section cast

/-!
### Images under `Fin.cast`
-/

@[simp]
/--
theorem `finsetImage_cast_Icc` / 定理 `finsetImage_cast_Icc`

English:
theorem finsetImage_cast_Icc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Icc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).image (.cast h) = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Ico` / 定理 `finsetImage_cast_Ico`

English:
theorem finsetImage_cast_Ico
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Ico
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).image (.cast h) = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Ioc` / 定理 `finsetImage_cast_Ioc`

English:
theorem finsetImage_cast_Ioc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Ioc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).image (.cast h) = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Ioo` / 定理 `finsetImage_cast_Ioo`

English:
theorem finsetImage_cast_Ioo
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Ioo
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).image (.cast h) = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_uIcc` / 定理 `finsetImage_cast_uIcc`

English:
theorem finsetImage_cast_uIcc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_uIcc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).image (.cast h) = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Ici` / 定理 `finsetImage_cast_Ici`

English:
theorem finsetImage_cast_Ici
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Ici
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Ici (h : n = m) (i : Fin n) :
    (Ici i).image (.cast h) = Ici (i.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Ioi` / 定理 `finsetImage_cast_Ioi`

English:
theorem finsetImage_cast_Ioi
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Ioi
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).image (.cast h) = Ioi (i.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Iic` / 定理 `finsetImage_cast_Iic`

English:
theorem finsetImage_cast_Iic
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_cast_Iic
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Iic (h : n = m) (i : Fin n) :
    (Iic i).image (.cast h) = Iic (i.cast h) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_cast_Iio` / 定理 `finsetImage_cast_Iio`

English:
theorem finsetImage_cast_Iio
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 finsetImage_cast_Iio
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_cast_Iio (h : n = m) (i : Fin n) :
    (Iio i).image (.cast h) = Iio (i.cast h) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `finCongr`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Icc` / 定理 `map_finCongr_Icc`

English:
theorem map_finCongr_Icc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Icc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).map (finCongr h).toEmbedding = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Ico` / 定理 `map_finCongr_Ico`

English:
theorem map_finCongr_Ico
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Ico
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).map (finCongr h).toEmbedding = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Ioc` / 定理 `map_finCongr_Ioc`

English:
theorem map_finCongr_Ioc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Ioc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).map (finCongr h).toEmbedding = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Ioo` / 定理 `map_finCongr_Ioo`

English:
theorem map_finCongr_Ioo
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Ioo
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).map (finCongr h).toEmbedding = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_uIcc` / 定理 `map_finCongr_uIcc`

English:
theorem map_finCongr_uIcc
  given: (h : n = m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_uIcc
  条件: (h : n = m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).map (finCongr h).toEmbedding = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Ici` / 定理 `map_finCongr_Ici`

English:
theorem map_finCongr_Ici
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Ici
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Ici (h : n = m) (i : Fin n) :
    (Ici i).map (finCongr h).toEmbedding = Ici (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Ioi` / 定理 `map_finCongr_Ioi`

English:
theorem map_finCongr_Ioi
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Ioi
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).map (finCongr h).toEmbedding = Ioi (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Iic` / 定理 `map_finCongr_Iic`

English:
theorem map_finCongr_Iic
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Iic
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Iic (h : n = m) (i : Fin n) :
    (Iic i).map (finCongr h).toEmbedding = Iic (i.cast h) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_finCongr_Iio` / 定理 `map_finCongr_Iio`

English:
theorem map_finCongr_Iio
  given: (h : n = m) (i : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_finCongr_Iio
  条件: (h : n = m) (i : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_finCongr_Iio (h : n = m) (i : Fin n) :
    (Iio i).map (finCongr h).toEmbedding = Iio (i.cast h) := by
  simp [← coe_inj]

end cast

section castSucc

/-!
### Images under `Fin.castSucc`
-/

@[simp]
/--
theorem `finsetImage_castSucc_Icc` / 定理 `finsetImage_castSucc_Icc`

English:
theorem finsetImage_castSucc_Icc
  given: (i j : Fin n)
  proof: finsetImage_castAdd_Icc ..

@[simp]

中文:
定理 finsetImage_castSucc_Icc
  条件: (i j : Fin n)
  证明: finsetImage_castAdd_Icc ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Icc
-/
theorem finsetImage_castSucc_Icc (i j : Fin n) :
    (Icc i j).image castSucc = Icc i.castSucc j.castSucc :=
  finsetImage_castAdd_Icc ..

@[simp]
/--
theorem `finsetImage_castSucc_Ico` / 定理 `finsetImage_castSucc_Ico`

English:
theorem finsetImage_castSucc_Ico
  given: (i j : Fin n)
  proof: finsetImage_castAdd_Ico ..

@[simp]

中文:
定理 finsetImage_castSucc_Ico
  条件: (i j : Fin n)
  证明: finsetImage_castAdd_Ico ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Ico
-/
theorem finsetImage_castSucc_Ico (i j : Fin n) :
    (Ico i j).image castSucc = Ico i.castSucc j.castSucc :=
  finsetImage_castAdd_Ico ..

@[simp]
/--
theorem `finsetImage_castSucc_Ioc` / 定理 `finsetImage_castSucc_Ioc`

English:
theorem finsetImage_castSucc_Ioc
  given: (i j : Fin n)
  proof: finsetImage_castAdd_Ioc ..

@[simp]

中文:
定理 finsetImage_castSucc_Ioc
  条件: (i j : Fin n)
  证明: finsetImage_castAdd_Ioc ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Ioc
-/
theorem finsetImage_castSucc_Ioc (i j : Fin n) :
    (Ioc i j).image castSucc = Ioc i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioc ..

@[simp]
/--
theorem `finsetImage_castSucc_Ioo` / 定理 `finsetImage_castSucc_Ioo`

English:
theorem finsetImage_castSucc_Ioo
  given: (i j : Fin n)
  proof: finsetImage_castAdd_Ioo ..

@[simp]

中文:
定理 finsetImage_castSucc_Ioo
  条件: (i j : Fin n)
  证明: finsetImage_castAdd_Ioo ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Ioo
-/
theorem finsetImage_castSucc_Ioo (i j : Fin n) :
    (Ioo i j).image castSucc = Ioo i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioo ..

@[simp]
/--
theorem `finsetImage_castSucc_uIcc` / 定理 `finsetImage_castSucc_uIcc`

English:
theorem finsetImage_castSucc_uIcc
  given: (i j : Fin n)
  proof: finsetImage_castAdd_uIcc ..

@[simp]

中文:
定理 finsetImage_castSucc_uIcc
  条件: (i j : Fin n)
  证明: finsetImage_castAdd_uIcc ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_uIcc
-/
theorem finsetImage_castSucc_uIcc (i j : Fin n) :
    (uIcc i j).image castSucc = uIcc i.castSucc j.castSucc :=
  finsetImage_castAdd_uIcc ..

@[simp]
/--
theorem `finsetImage_castSucc_Ici` / 定理 `finsetImage_castSucc_Ici`

English:
theorem finsetImage_castSucc_Ici
  given: (i : Fin n)
  statement: (Ici i).image castSucc = Ico i.castSucc (.last n)
  proof: finsetImage_castAdd_Ici ..

@[simp]

中文:
定理 finsetImage_castSucc_Ici
  条件: (i : Fin n)
  结论: (Ici i).image castSucc = Ico i.castSucc (.last n)
  证明: finsetImage_castAdd_Ici ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Ici
-/
theorem finsetImage_castSucc_Ici (i : Fin n) : (Ici i).image castSucc = Ico i.castSucc (.last n) :=
  finsetImage_castAdd_Ici ..

@[simp]
/--
theorem `finsetImage_castSucc_Ioi` / 定理 `finsetImage_castSucc_Ioi`

English:
theorem finsetImage_castSucc_Ioi
  given: (i : Fin n)
  statement: (Ioi i).image castSucc = Ioo i.castSucc (.last n)
  proof: finsetImage_castAdd_Ioi ..

@[simp]

中文:
定理 finsetImage_castSucc_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).image castSucc = Ioo i.castSucc (.last n)
  证明: finsetImage_castAdd_Ioi ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Ioi
-/
theorem finsetImage_castSucc_Ioi (i : Fin n) : (Ioi i).image castSucc = Ioo i.castSucc (.last n) :=
  finsetImage_castAdd_Ioi ..

@[simp]
/--
theorem `finsetImage_castSucc_Iic` / 定理 `finsetImage_castSucc_Iic`

English:
theorem finsetImage_castSucc_Iic
  given: (i : Fin n)
  statement: (Iic i).image castSucc = Iic i.castSucc
  proof: finsetImage_castAdd_Iic ..

@[simp]

中文:
定理 finsetImage_castSucc_Iic
  条件: (i : Fin n)
  结论: (Iic i).image castSucc = Iic i.castSucc
  证明: finsetImage_castAdd_Iic ..

@[simp]

Depends on / 依赖: finsetImage_castAdd_Iic
-/
theorem finsetImage_castSucc_Iic (i : Fin n) : (Iic i).image castSucc = Iic i.castSucc :=
  finsetImage_castAdd_Iic ..

@[simp]
/--
theorem `finsetImage_castSucc_Iio` / 定理 `finsetImage_castSucc_Iio`

English:
theorem finsetImage_castSucc_Iio
  given: (i : Fin n)
  statement: (Iio i).image castSucc = Iio i.castSucc
  proof: finsetImage_castAdd_Iio ..

中文:
定理 finsetImage_castSucc_Iio
  条件: (i : Fin n)
  结论: (Iio i).image castSucc = Iio i.castSucc
  证明: finsetImage_castAdd_Iio ..

Depends on / 依赖: finsetImage_castAdd_Iio
-/
theorem finsetImage_castSucc_Iio (i : Fin n) : (Iio i).image castSucc = Iio i.castSucc :=
  finsetImage_castAdd_Iio ..

/-!
### `Finset.map` along `Fin.castSuccEmb`
-/

@[simp]
/--
theorem `map_castSuccEmb_Icc` / 定理 `map_castSuccEmb_Icc`

English:
theorem map_castSuccEmb_Icc
  given: (i j : Fin n)
  proof: map_castAddEmb_Icc ..

@[simp]

中文:
定理 map_castSuccEmb_Icc
  条件: (i j : Fin n)
  证明: map_castAddEmb_Icc ..

@[simp]

Depends on / 依赖: map_castAddEmb_Icc
-/
theorem map_castSuccEmb_Icc (i j : Fin n) :
    (Icc i j).map castSuccEmb = Icc i.castSucc j.castSucc :=
  map_castAddEmb_Icc ..

@[simp]
/--
theorem `map_castSuccEmb_Ico` / 定理 `map_castSuccEmb_Ico`

English:
theorem map_castSuccEmb_Ico
  given: (i j : Fin n)
  proof: map_castAddEmb_Ico ..

@[simp]

中文:
定理 map_castSuccEmb_Ico
  条件: (i j : Fin n)
  证明: map_castAddEmb_Ico ..

@[simp]

Depends on / 依赖: map_castAddEmb_Ico
-/
theorem map_castSuccEmb_Ico (i j : Fin n) :
    (Ico i j).map castSuccEmb = Ico i.castSucc j.castSucc :=
  map_castAddEmb_Ico ..

@[simp]
/--
theorem `map_castSuccEmb_Ioc` / 定理 `map_castSuccEmb_Ioc`

English:
theorem map_castSuccEmb_Ioc
  given: (i j : Fin n)
  proof: map_castAddEmb_Ioc ..

@[simp]

中文:
定理 map_castSuccEmb_Ioc
  条件: (i j : Fin n)
  证明: map_castAddEmb_Ioc ..

@[simp]

Depends on / 依赖: map_castAddEmb_Ioc
-/
theorem map_castSuccEmb_Ioc (i j : Fin n) :
    (Ioc i j).map castSuccEmb = Ioc i.castSucc j.castSucc :=
  map_castAddEmb_Ioc ..

@[simp]
/--
theorem `map_castSuccEmb_Ioo` / 定理 `map_castSuccEmb_Ioo`

English:
theorem map_castSuccEmb_Ioo
  given: (i j : Fin n)
  proof: map_castAddEmb_Ioo ..

@[simp]

中文:
定理 map_castSuccEmb_Ioo
  条件: (i j : Fin n)
  证明: map_castAddEmb_Ioo ..

@[simp]

Depends on / 依赖: map_castAddEmb_Ioo
-/
theorem map_castSuccEmb_Ioo (i j : Fin n) :
    (Ioo i j).map castSuccEmb = Ioo i.castSucc j.castSucc :=
  map_castAddEmb_Ioo ..

@[simp]
/--
theorem `map_castSuccEmb_uIcc` / 定理 `map_castSuccEmb_uIcc`

English:
theorem map_castSuccEmb_uIcc
  given: (i j : Fin n)
  proof: map_castAddEmb_uIcc ..

@[simp]

中文:
定理 map_castSuccEmb_uIcc
  条件: (i j : Fin n)
  证明: map_castAddEmb_uIcc ..

@[simp]

Depends on / 依赖: map_castAddEmb_uIcc
-/
theorem map_castSuccEmb_uIcc (i j : Fin n) :
    (uIcc i j).map castSuccEmb = uIcc i.castSucc j.castSucc :=
  map_castAddEmb_uIcc ..

@[simp]
/--
theorem `map_castSuccEmb_Ici` / 定理 `map_castSuccEmb_Ici`

English:
theorem map_castSuccEmb_Ici
  given: (i : Fin n)
  statement: (Ici i).map castSuccEmb = Ico i.castSucc (.last n)
  proof: map_castAddEmb_Ici ..

@[simp]

中文:
定理 map_castSuccEmb_Ici
  条件: (i : Fin n)
  结论: (Ici i).map castSuccEmb = Ico i.castSucc (.last n)
  证明: map_castAddEmb_Ici ..

@[simp]

Depends on / 依赖: map_castAddEmb_Ici
-/
theorem map_castSuccEmb_Ici (i : Fin n) : (Ici i).map castSuccEmb = Ico i.castSucc (.last n) :=
  map_castAddEmb_Ici ..

@[simp]
/--
theorem `map_castSuccEmb_Ioi` / 定理 `map_castSuccEmb_Ioi`

English:
theorem map_castSuccEmb_Ioi
  given: (i : Fin n)
  statement: (Ioi i).map castSuccEmb = Ioo i.castSucc (.last n)
  proof: map_castAddEmb_Ioi ..

@[simp]

中文:
定理 map_castSuccEmb_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).map castSuccEmb = Ioo i.castSucc (.last n)
  证明: map_castAddEmb_Ioi ..

@[simp]

Depends on / 依赖: map_castAddEmb_Ioi
-/
theorem map_castSuccEmb_Ioi (i : Fin n) : (Ioi i).map castSuccEmb = Ioo i.castSucc (.last n) :=
  map_castAddEmb_Ioi ..

@[simp]
/--
theorem `map_castSuccEmb_Iic` / 定理 `map_castSuccEmb_Iic`

English:
theorem map_castSuccEmb_Iic
  given: (i : Fin n)
  statement: (Iic i).map castSuccEmb = Iic i.castSucc
  proof: map_castAddEmb_Iic ..

@[simp]

中文:
定理 map_castSuccEmb_Iic
  条件: (i : Fin n)
  结论: (Iic i).map castSuccEmb = Iic i.castSucc
  证明: map_castAddEmb_Iic ..

@[simp]

Depends on / 依赖: map_castAddEmb_Iic
-/
theorem map_castSuccEmb_Iic (i : Fin n) : (Iic i).map castSuccEmb = Iic i.castSucc :=
  map_castAddEmb_Iic ..

@[simp]
/--
theorem `map_castSuccEmb_Iio` / 定理 `map_castSuccEmb_Iio`

English:
theorem map_castSuccEmb_Iio
  given: (i : Fin n)
  statement: (Iio i).map castSuccEmb = Iio i.castSucc
  proof: map_castAddEmb_Iio ..

中文:
定理 map_castSuccEmb_Iio
  条件: (i : Fin n)
  结论: (Iio i).map castSuccEmb = Iio i.castSucc
  证明: map_castAddEmb_Iio ..

Depends on / 依赖: map_castAddEmb_Iio
-/
theorem map_castSuccEmb_Iio (i : Fin n) : (Iio i).map castSuccEmb = Iio i.castSucc :=
  map_castAddEmb_Iio ..

end castSucc

section natAdd

/-!
### Images under `Fin.natAdd`
-/

@[simp]
/--
theorem `finsetImage_natAdd_Icc` / 定理 `finsetImage_natAdd_Icc`

English:
theorem finsetImage_natAdd_Icc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_Icc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (natAdd m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_Ico` / 定理 `finsetImage_natAdd_Ico`

English:
theorem finsetImage_natAdd_Ico
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_Ico
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (natAdd m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_Ioc` / 定理 `finsetImage_natAdd_Ioc`

English:
theorem finsetImage_natAdd_Ioc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (natAdd m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_Ioo` / 定理 `finsetImage_natAdd_Ioo`

English:
theorem finsetImage_natAdd_Ioo
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (natAdd m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_uIcc` / 定理 `finsetImage_natAdd_uIcc`

English:
theorem finsetImage_natAdd_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (natAdd m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_Ici` / 定理 `finsetImage_natAdd_Ici`

English:
theorem finsetImage_natAdd_Ici
  given: (m) (i : Fin n)
  statement: (Ici i).image (natAdd m) = Ici (natAdd m i)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_natAdd_Ici
  条件: (m) (i : Fin n)
  结论: (Ici i).image (natAdd m) = Ici (natAdd m i)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Ici (m) (i : Fin n) : (Ici i).image (natAdd m) = Ici (natAdd m i) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_natAdd_Ioi` / 定理 `finsetImage_natAdd_Ioi`

English:
theorem finsetImage_natAdd_Ioi
  given: (m) (i : Fin n)
  statement: (Ioi i).image (natAdd m) = Ioi (natAdd m i)
  proof: by
  simp [← coe_inj]

中文:
定理 finsetImage_natAdd_Ioi
  条件: (m) (i : Fin n)
  结论: (Ioi i).image (natAdd m) = Ioi (natAdd m i)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_natAdd_Ioi (m) (i : Fin n) : (Ioi i).image (natAdd m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.natAddEmb`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Icc` / 定理 `map_natAddEmb_Icc`

English:
theorem map_natAddEmb_Icc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Icc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (natAddEmb m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Ico` / 定理 `map_natAddEmb_Ico`

English:
theorem map_natAddEmb_Ico
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Ico
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (natAddEmb m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Ioc` / 定理 `map_natAddEmb_Ioc`

English:
theorem map_natAddEmb_Ioc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (natAddEmb m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Ioo` / 定理 `map_natAddEmb_Ioo`

English:
theorem map_natAddEmb_Ioo
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (natAddEmb m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_uIcc` / 定理 `map_natAddEmb_uIcc`

English:
theorem map_natAddEmb_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (natAddEmb m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Ici` / 定理 `map_natAddEmb_Ici`

English:
theorem map_natAddEmb_Ici
  given: (m) (i : Fin n)
  statement: (Ici i).map (natAddEmb m) = Ici (natAdd m i)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Ici
  条件: (m) (i : Fin n)
  结论: (Ici i).map (natAddEmb m) = Ici (natAdd m i)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Ici (m) (i : Fin n) : (Ici i).map (natAddEmb m) = Ici (natAdd m i) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_natAddEmb_Ioi` / 定理 `map_natAddEmb_Ioi`

English:
theorem map_natAddEmb_Ioi
  given: (m) (i : Fin n)
  statement: (Ioi i).map (natAddEmb m) = Ioi (natAdd m i)
  proof: by
  simp [← coe_inj]

中文:
定理 map_natAddEmb_Ioi
  条件: (m) (i : Fin n)
  结论: (Ioi i).map (natAddEmb m) = Ioi (natAdd m i)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_natAddEmb_Ioi (m) (i : Fin n) : (Ioi i).map (natAddEmb m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

end natAdd

section addNat

/-!
### Images under `Fin.addNat`
-/

@[simp]
/--
theorem `finsetImage_addNat_Icc` / 定理 `finsetImage_addNat_Icc`

English:
theorem finsetImage_addNat_Icc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_Icc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Icc (m) (i j : Fin n) :
    (Icc i j).image (addNat · m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_Ico` / 定理 `finsetImage_addNat_Ico`

English:
theorem finsetImage_addNat_Ico
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_Ico
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Ico (m) (i j : Fin n) :
    (Ico i j).image (addNat · m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_Ioc` / 定理 `finsetImage_addNat_Ioc`

English:
theorem finsetImage_addNat_Ioc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (addNat · m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_Ioo` / 定理 `finsetImage_addNat_Ioo`

English:
theorem finsetImage_addNat_Ioo
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (addNat · m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_uIcc` / 定理 `finsetImage_addNat_uIcc`

English:
theorem finsetImage_addNat_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (addNat · m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_Ici` / 定理 `finsetImage_addNat_Ici`

English:
theorem finsetImage_addNat_Ici
  given: (m) (i : Fin n)
  statement: (Ici i).image (addNat · m) = Ici (i.addNat m)
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_addNat_Ici
  条件: (m) (i : Fin n)
  结论: (Ici i).image (add自然数 · m) = Ici (i.add自然数 m)
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Ici (m) (i : Fin n) : (Ici i).image (addNat · m) = Ici (i.addNat m) := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_addNat_Ioi` / 定理 `finsetImage_addNat_Ioi`

English:
theorem finsetImage_addNat_Ioi
  given: (m) (i : Fin n)
  statement: (Ioi i).image (addNat · m) = Ioi (i.addNat m)
  proof: by
  simp [← coe_inj]

中文:
定理 finsetImage_addNat_Ioi
  条件: (m) (i : Fin n)
  结论: (Ioi i).image (add自然数 · m) = Ioi (i.add自然数 m)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_addNat_Ioi (m) (i : Fin n) : (Ioi i).image (addNat · m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.addNatEmb`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Icc` / 定理 `map_addNatEmb_Icc`

English:
theorem map_addNatEmb_Icc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Icc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (addNatEmb m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Ico` / 定理 `map_addNatEmb_Ico`

English:
theorem map_addNatEmb_Ico
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Ico
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (addNatEmb m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Ioc` / 定理 `map_addNatEmb_Ioc`

English:
theorem map_addNatEmb_Ioc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Ioc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (addNatEmb m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Ioo` / 定理 `map_addNatEmb_Ioo`

English:
theorem map_addNatEmb_Ioo
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Ioo
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (addNatEmb m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_uIcc` / 定理 `map_addNatEmb_uIcc`

English:
theorem map_addNatEmb_uIcc
  given: (m) (i j : Fin n)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_uIcc
  条件: (m) (i j : Fin n)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (addNatEmb m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Ici` / 定理 `map_addNatEmb_Ici`

English:
theorem map_addNatEmb_Ici
  given: (m) (i : Fin n)
  statement: (Ici i).map (addNatEmb m) = Ici (i.addNat m)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Ici
  条件: (m) (i : Fin n)
  结论: (Ici i).map (add自然数Emb m) = Ici (i.add自然数 m)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Ici (m) (i : Fin n) : (Ici i).map (addNatEmb m) = Ici (i.addNat m) := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_addNatEmb_Ioi` / 定理 `map_addNatEmb_Ioi`

English:
theorem map_addNatEmb_Ioi
  given: (m) (i : Fin n)
  statement: (Ioi i).map (addNatEmb m) = Ioi (i.addNat m)
  proof: by
  simp [← coe_inj]

中文:
定理 map_addNatEmb_Ioi
  条件: (m) (i : Fin n)
  结论: (Ioi i).map (add自然数Emb m) = Ioi (i.add自然数 m)
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_addNatEmb_Ioi (m) (i : Fin n) : (Ioi i).map (addNatEmb m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

end addNat

section succ

/-!
### Images under `Fin.succ`
-/

@[simp]
/--
theorem `finsetImage_succ_Icc` / 定理 `finsetImage_succ_Icc`

English:
theorem finsetImage_succ_Icc
  given: (i j : Fin n)
  statement: (Icc i j).image succ = Icc i.succ j.succ
  proof: finsetImage_addNat_Icc ..

@[simp]

中文:
定理 finsetImage_succ_Icc
  条件: (i j : Fin n)
  结论: (Icc i j).image succ = Icc i.succ j.succ
  证明: finsetImage_addNat_Icc ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Icc
-/
theorem finsetImage_succ_Icc (i j : Fin n) : (Icc i j).image succ = Icc i.succ j.succ :=
  finsetImage_addNat_Icc ..

@[simp]
/--
theorem `finsetImage_succ_Ico` / 定理 `finsetImage_succ_Ico`

English:
theorem finsetImage_succ_Ico
  given: (i j : Fin n)
  statement: (Ico i j).image succ = Ico i.succ j.succ
  proof: finsetImage_addNat_Ico ..

@[simp]

中文:
定理 finsetImage_succ_Ico
  条件: (i j : Fin n)
  结论: (Ico i j).image succ = Ico i.succ j.succ
  证明: finsetImage_addNat_Ico ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Ico
-/
theorem finsetImage_succ_Ico (i j : Fin n) : (Ico i j).image succ = Ico i.succ j.succ :=
  finsetImage_addNat_Ico ..

@[simp]
/--
theorem `finsetImage_succ_Ioc` / 定理 `finsetImage_succ_Ioc`

English:
theorem finsetImage_succ_Ioc
  given: (i j : Fin n)
  statement: (Ioc i j).image succ = Ioc i.succ j.succ
  proof: finsetImage_addNat_Ioc ..

@[simp]

中文:
定理 finsetImage_succ_Ioc
  条件: (i j : Fin n)
  结论: (Ioc i j).image succ = Ioc i.succ j.succ
  证明: finsetImage_addNat_Ioc ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Ioc
-/
theorem finsetImage_succ_Ioc (i j : Fin n) : (Ioc i j).image succ = Ioc i.succ j.succ :=
  finsetImage_addNat_Ioc ..

@[simp]
/--
theorem `finsetImage_succ_Ioo` / 定理 `finsetImage_succ_Ioo`

English:
theorem finsetImage_succ_Ioo
  given: (i j : Fin n)
  statement: (Ioo i j).image succ = Ioo i.succ j.succ
  proof: finsetImage_addNat_Ioo ..

@[simp]

中文:
定理 finsetImage_succ_Ioo
  条件: (i j : Fin n)
  结论: (Ioo i j).image succ = Ioo i.succ j.succ
  证明: finsetImage_addNat_Ioo ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Ioo
-/
theorem finsetImage_succ_Ioo (i j : Fin n) : (Ioo i j).image succ = Ioo i.succ j.succ :=
  finsetImage_addNat_Ioo ..

@[simp]
/--
theorem `finsetImage_succ_uIcc` / 定理 `finsetImage_succ_uIcc`

English:
theorem finsetImage_succ_uIcc
  given: (i j : Fin n)
  statement: (uIcc i j).image succ = uIcc i.succ j.succ
  proof: finsetImage_addNat_uIcc ..

@[simp]

中文:
定理 finsetImage_succ_uIcc
  条件: (i j : Fin n)
  结论: (uIcc i j).image succ = uIcc i.succ j.succ
  证明: finsetImage_addNat_uIcc ..

@[simp]

Depends on / 依赖: finsetImage_addNat_uIcc
-/
theorem finsetImage_succ_uIcc (i j : Fin n) : (uIcc i j).image succ = uIcc i.succ j.succ :=
  finsetImage_addNat_uIcc ..

@[simp]
/--
theorem `finsetImage_succ_Ici` / 定理 `finsetImage_succ_Ici`

English:
theorem finsetImage_succ_Ici
  given: (i : Fin n)
  statement: (Ici i).image succ = Ici i.succ
  proof: finsetImage_addNat_Ici ..

@[simp]

中文:
定理 finsetImage_succ_Ici
  条件: (i : Fin n)
  结论: (Ici i).image succ = Ici i.succ
  证明: finsetImage_addNat_Ici ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Ici
-/
theorem finsetImage_succ_Ici (i : Fin n) : (Ici i).image succ = Ici i.succ :=
  finsetImage_addNat_Ici ..

@[simp]
/--
theorem `finsetImage_succ_Ioi` / 定理 `finsetImage_succ_Ioi`

English:
theorem finsetImage_succ_Ioi
  given: (i : Fin n)
  statement: (Ioi i).image succ = Ioi i.succ
  proof: finsetImage_addNat_Ioi ..

@[simp]

中文:
定理 finsetImage_succ_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).image succ = Ioi i.succ
  证明: finsetImage_addNat_Ioi ..

@[simp]

Depends on / 依赖: finsetImage_addNat_Ioi
-/
theorem finsetImage_succ_Ioi (i : Fin n) : (Ioi i).image succ = Ioi i.succ :=
  finsetImage_addNat_Ioi ..

@[simp]
/--
theorem `finsetImage_succ_Iic` / 定理 `finsetImage_succ_Iic`

English:
theorem finsetImage_succ_Iic
  given: (i : Fin n)
  statement: (Iic i).image succ = Ioc 0 i.succ
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_succ_Iic
  条件: (i : Fin n)
  结论: (Iic i).image succ = Ioc 0 i.succ
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_succ_Iic (i : Fin n) : (Iic i).image succ = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_succ_Iio` / 定理 `finsetImage_succ_Iio`

English:
theorem finsetImage_succ_Iio
  given: (i : Fin n)
  statement: (Iio i).image succ = Ioo 0 i.succ
  proof: by
  simp [← coe_inj]

中文:
定理 finsetImage_succ_Iio
  条件: (i : Fin n)
  结论: (Iio i).image succ = Ioo 0 i.succ
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_succ_Iio (i : Fin n) : (Iio i).image succ = Ioo 0 i.succ := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.succEmb`
-/

@[simp]
/--
theorem `map_succEmb_Icc` / 定理 `map_succEmb_Icc`

English:
theorem map_succEmb_Icc
  given: (i j : Fin n)
  statement: (Icc i j).map (succEmb n) = Icc i.succ j.succ
  proof: map_addNatEmb_Icc ..

@[simp]

中文:
定理 map_succEmb_Icc
  条件: (i j : Fin n)
  结论: (Icc i j).map (succEmb n) = Icc i.succ j.succ
  证明: map_addNatEmb_Icc ..

@[simp]

Depends on / 依赖: map_addNatEmb_Icc
-/
theorem map_succEmb_Icc (i j : Fin n) : (Icc i j).map (succEmb n) = Icc i.succ j.succ :=
  map_addNatEmb_Icc ..

@[simp]
/--
theorem `map_succEmb_Ico` / 定理 `map_succEmb_Ico`

English:
theorem map_succEmb_Ico
  given: (i j : Fin n)
  statement: (Ico i j).map (succEmb n) = Ico i.succ j.succ
  proof: map_addNatEmb_Ico ..

@[simp]

中文:
定理 map_succEmb_Ico
  条件: (i j : Fin n)
  结论: (Ico i j).map (succEmb n) = Ico i.succ j.succ
  证明: map_addNatEmb_Ico ..

@[simp]

Depends on / 依赖: map_addNatEmb_Ico
-/
theorem map_succEmb_Ico (i j : Fin n) : (Ico i j).map (succEmb n) = Ico i.succ j.succ :=
  map_addNatEmb_Ico ..

@[simp]
/--
theorem `map_succEmb_Ioc` / 定理 `map_succEmb_Ioc`

English:
theorem map_succEmb_Ioc
  given: (i j : Fin n)
  statement: (Ioc i j).map (succEmb n) = Ioc i.succ j.succ
  proof: map_addNatEmb_Ioc ..

@[simp]

中文:
定理 map_succEmb_Ioc
  条件: (i j : Fin n)
  结论: (Ioc i j).map (succEmb n) = Ioc i.succ j.succ
  证明: map_addNatEmb_Ioc ..

@[simp]

Depends on / 依赖: map_addNatEmb_Ioc
-/
theorem map_succEmb_Ioc (i j : Fin n) : (Ioc i j).map (succEmb n) = Ioc i.succ j.succ :=
  map_addNatEmb_Ioc ..

@[simp]
/--
theorem `map_succEmb_Ioo` / 定理 `map_succEmb_Ioo`

English:
theorem map_succEmb_Ioo
  given: (i j : Fin n)
  statement: (Ioo i j).map (succEmb n) = Ioo i.succ j.succ
  proof: map_addNatEmb_Ioo ..

@[simp]

中文:
定理 map_succEmb_Ioo
  条件: (i j : Fin n)
  结论: (Ioo i j).map (succEmb n) = Ioo i.succ j.succ
  证明: map_addNatEmb_Ioo ..

@[simp]

Depends on / 依赖: map_addNatEmb_Ioo
-/
theorem map_succEmb_Ioo (i j : Fin n) : (Ioo i j).map (succEmb n) = Ioo i.succ j.succ :=
  map_addNatEmb_Ioo ..

@[simp]
/--
theorem `map_succEmb_uIcc` / 定理 `map_succEmb_uIcc`

English:
theorem map_succEmb_uIcc
  given: (i j : Fin n)
  statement: (uIcc i j).map (succEmb n) = uIcc i.succ j.succ
  proof: map_addNatEmb_uIcc ..

@[simp]

中文:
定理 map_succEmb_uIcc
  条件: (i j : Fin n)
  结论: (uIcc i j).map (succEmb n) = uIcc i.succ j.succ
  证明: map_addNatEmb_uIcc ..

@[simp]

Depends on / 依赖: map_addNatEmb_uIcc
-/
theorem map_succEmb_uIcc (i j : Fin n) : (uIcc i j).map (succEmb n) = uIcc i.succ j.succ :=
  map_addNatEmb_uIcc ..

@[simp]
/--
theorem `map_succEmb_Ici` / 定理 `map_succEmb_Ici`

English:
theorem map_succEmb_Ici
  given: (i : Fin n)
  statement: (Ici i).map (succEmb n) = Ici i.succ
  proof: map_addNatEmb_Ici ..

@[simp]

中文:
定理 map_succEmb_Ici
  条件: (i : Fin n)
  结论: (Ici i).map (succEmb n) = Ici i.succ
  证明: map_addNatEmb_Ici ..

@[simp]

Depends on / 依赖: map_addNatEmb_Ici
-/
theorem map_succEmb_Ici (i : Fin n) : (Ici i).map (succEmb n) = Ici i.succ :=
  map_addNatEmb_Ici ..

@[simp]
/--
theorem `map_succEmb_Ioi` / 定理 `map_succEmb_Ioi`

English:
theorem map_succEmb_Ioi
  given: (i : Fin n)
  statement: (Ioi i).map (succEmb n) = Ioi i.succ
  proof: map_addNatEmb_Ioi ..

@[simp]

中文:
定理 map_succEmb_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).map (succEmb n) = Ioi i.succ
  证明: map_addNatEmb_Ioi ..

@[simp]

Depends on / 依赖: map_addNatEmb_Ioi
-/
theorem map_succEmb_Ioi (i : Fin n) : (Ioi i).map (succEmb n) = Ioi i.succ :=
  map_addNatEmb_Ioi ..

@[simp]
/--
theorem `map_succEmb_Iic` / 定理 `map_succEmb_Iic`

English:
theorem map_succEmb_Iic
  given: (i : Fin n)
  statement: (Iic i).map (succEmb n) = Ioc 0 i.succ
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 map_succEmb_Iic
  条件: (i : Fin n)
  结论: (Iic i).map (succEmb n) = Ioc 0 i.succ
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem map_succEmb_Iic (i : Fin n) : (Iic i).map (succEmb n) = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
/--
theorem `map_succEmb_Iio` / 定理 `map_succEmb_Iio`

English:
theorem map_succEmb_Iio
  given: (i : Fin n)
  statement: (Iio i).map (succEmb n) = Ioo 0 i.succ
  proof: by
  simp [← coe_inj]

中文:
定理 map_succEmb_Iio
  条件: (i : Fin n)
  结论: (Iio i).map (succEmb n) = Ioo 0 i.succ
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_succEmb_Iio (i : Fin n) : (Iio i).map (succEmb n) = Ioo 0 i.succ := by
  simp [← coe_inj]

end succ

section rev

/-!
### Images under `Fin.rev`
-/

@[simp]
/--
theorem `finsetImage_rev_Icc` / 定理 `finsetImage_rev_Icc`

English:
theorem finsetImage_rev_Icc
  given: (i j : Fin n)
  statement: (Icc i j).image rev = Icc j.rev i.rev
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Icc
  条件: (i j : Fin n)
  结论: (Icc i j).image rev = Icc j.rev i.rev
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Icc (i j : Fin n) : (Icc i j).image rev = Icc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Ico` / 定理 `finsetImage_rev_Ico`

English:
theorem finsetImage_rev_Ico
  given: (i j : Fin n)
  statement: (Ico i j).image rev = Ioc j.rev i.rev
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Ico
  条件: (i j : Fin n)
  结论: (Ico i j).image rev = Ioc j.rev i.rev
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Ico (i j : Fin n) : (Ico i j).image rev = Ioc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Ioc` / 定理 `finsetImage_rev_Ioc`

English:
theorem finsetImage_rev_Ioc
  given: (i j : Fin n)
  statement: (Ioc i j).image rev = Ico j.rev i.rev
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Ioc
  条件: (i j : Fin n)
  结论: (Ioc i j).image rev = Ico j.rev i.rev
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Ioc (i j : Fin n) : (Ioc i j).image rev = Ico j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Ioo` / 定理 `finsetImage_rev_Ioo`

English:
theorem finsetImage_rev_Ioo
  given: (i j : Fin n)
  statement: (Ioo i j).image rev = Ioo j.rev i.rev
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Ioo
  条件: (i j : Fin n)
  结论: (Ioo i j).image rev = Ioo j.rev i.rev
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Ioo (i j : Fin n) : (Ioo i j).image rev = Ioo j.rev i.rev := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_uIcc` / 定理 `finsetImage_rev_uIcc`

English:
theorem finsetImage_rev_uIcc
  given: (i j : Fin n)
  statement: (uIcc i j).image rev = uIcc i.rev j.rev
  proof: by
  simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_uIcc
  条件: (i j : Fin n)
  结论: (uIcc i j).image rev = uIcc i.rev j.rev
  证明: by
  simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_uIcc (i j : Fin n) : (uIcc i j).image rev = uIcc i.rev j.rev := by
  simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Ici` / 定理 `finsetImage_rev_Ici`

English:
theorem finsetImage_rev_Ici
  given: (i : Fin n)
  statement: (Ici i).image rev = Iic i.rev
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Ici
  条件: (i : Fin n)
  结论: (Ici i).image rev = Iic i.rev
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Ici (i : Fin n) : (Ici i).image rev = Iic i.rev := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Ioi` / 定理 `finsetImage_rev_Ioi`

English:
theorem finsetImage_rev_Ioi
  given: (i : Fin n)
  statement: (Ioi i).image rev = Iio i.rev
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).image rev = Iio i.rev
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Ioi (i : Fin n) : (Ioi i).image rev = Iio i.rev := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Iic` / 定理 `finsetImage_rev_Iic`

English:
theorem finsetImage_rev_Iic
  given: (i : Fin n)
  statement: (Iic i).image rev = Ici i.rev
  proof: by simp [← coe_inj]

@[simp]

中文:
定理 finsetImage_rev_Iic
  条件: (i : Fin n)
  结论: (Iic i).image rev = Ici i.rev
  证明: by simp [← coe_inj]

@[simp]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Iic (i : Fin n) : (Iic i).image rev = Ici i.rev := by simp [← coe_inj]

@[simp]
/--
theorem `finsetImage_rev_Iio` / 定理 `finsetImage_rev_Iio`

English:
theorem finsetImage_rev_Iio
  given: (i : Fin n)
  statement: (Iio i).image rev = Ioi i.rev
  proof: by simp [← coe_inj]

中文:
定理 finsetImage_rev_Iio
  条件: (i : Fin n)
  结论: (Iio i).image rev = Ioi i.rev
  证明: by simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem finsetImage_rev_Iio (i : Fin n) : (Iio i).image rev = Ioi i.rev := by simp [← coe_inj]

/-!
### `Finset.map` along `revPerm`
-/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Icc` / 定理 `map_revPerm_Icc`

English:
theorem map_revPerm_Icc
  given: (i j : Fin n)
  statement: (Icc i j).map revPerm.toEmbedding = Icc j.rev i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Icc
  条件: (i j : Fin n)
  结论: (Icc i j).map revPerm.toEmbedding = Icc j.rev i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Icc (i j : Fin n) : (Icc i j).map revPerm.toEmbedding = Icc j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Ico` / 定理 `map_revPerm_Ico`

English:
theorem map_revPerm_Ico
  given: (i j : Fin n)
  statement: (Ico i j).map revPerm.toEmbedding = Ioc j.rev i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Ico
  条件: (i j : Fin n)
  结论: (Ico i j).map revPerm.toEmbedding = Ioc j.rev i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Ico (i j : Fin n) : (Ico i j).map revPerm.toEmbedding = Ioc j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Ioc` / 定理 `map_revPerm_Ioc`

English:
theorem map_revPerm_Ioc
  given: (i j : Fin n)
  statement: (Ioc i j).map revPerm.toEmbedding = Ico j.rev i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Ioc
  条件: (i j : Fin n)
  结论: (Ioc i j).map revPerm.toEmbedding = Ico j.rev i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Ioc (i j : Fin n) : (Ioc i j).map revPerm.toEmbedding = Ico j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Ioo` / 定理 `map_revPerm_Ioo`

English:
theorem map_revPerm_Ioo
  given: (i j : Fin n)
  statement: (Ioo i j).map revPerm.toEmbedding = Ioo j.rev i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Ioo
  条件: (i j : Fin n)
  结论: (Ioo i j).map revPerm.toEmbedding = Ioo j.rev i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Ioo (i j : Fin n) : (Ioo i j).map revPerm.toEmbedding = Ioo j.rev i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_uIcc` / 定理 `map_revPerm_uIcc`

English:
theorem map_revPerm_uIcc
  given: (i j : Fin n)
  statement: (uIcc i j).map revPerm.toEmbedding = uIcc i.rev j.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_uIcc
  条件: (i j : Fin n)
  结论: (uIcc i j).map revPerm.toEmbedding = uIcc i.rev j.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_uIcc (i j : Fin n) : (uIcc i j).map revPerm.toEmbedding = uIcc i.rev j.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Ici` / 定理 `map_revPerm_Ici`

English:
theorem map_revPerm_Ici
  given: (i : Fin n)
  statement: (Ici i).map revPerm.toEmbedding = Iic i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Ici
  条件: (i : Fin n)
  结论: (Ici i).map revPerm.toEmbedding = Iic i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Ici (i : Fin n) : (Ici i).map revPerm.toEmbedding = Iic i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Ioi` / 定理 `map_revPerm_Ioi`

English:
theorem map_revPerm_Ioi
  given: (i : Fin n)
  statement: (Ioi i).map revPerm.toEmbedding = Iio i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Ioi
  条件: (i : Fin n)
  结论: (Ioi i).map revPerm.toEmbedding = Iio i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Ioi (i : Fin n) : (Ioi i).map revPerm.toEmbedding = Iio i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Iic` / 定理 `map_revPerm_Iic`

English:
theorem map_revPerm_Iic
  given: (i : Fin n)
  statement: (Iic i).map revPerm.toEmbedding = Ici i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Iic
  条件: (i : Fin n)
  结论: (Iic i).map revPerm.toEmbedding = Ici i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Iic (i : Fin n) : (Iic i).map revPerm.toEmbedding = Ici i.rev := by
  simp [← coe_inj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_revPerm_Iio` / 定理 `map_revPerm_Iio`

English:
theorem map_revPerm_Iio
  given: (i : Fin n)
  statement: (Iio i).map revPerm.toEmbedding = Ioi i.rev
  proof: by
  simp [← coe_inj]

中文:
定理 map_revPerm_Iio
  条件: (i : Fin n)
  结论: (Iio i).map revPerm.toEmbedding = Ioi i.rev
  证明: by
  simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem map_revPerm_Iio (i : Fin n) : (Iio i).map revPerm.toEmbedding = Ioi i.rev := by
  simp [← coe_inj]

end rev

/-!
### Cardinalities of the intervals
-/

section card

@[simp]
/--
lemma `card_Icc` / 引理 `card_Icc`

English:
lemma card_Icc
  statement: #(Icc a b) = b + 1 - a
  proof: by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]

中文:
引理 card_Icc
  结论: #(Icc a b) = b + 1 - a
  证明: by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]

Depends on / 依赖: Nat.card_Icc, card_Icc, card_map, map_valEmbedding_Icc
-/
lemma card_Icc : #(Icc a b) = b + 1 - a := by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]
/--
lemma `card_Ico` / 引理 `card_Ico`

English:
lemma card_Ico
  statement: #(Ico a b) = b - a
  proof: by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]

中文:
引理 card_Ico
  结论: #(Ico a b) = b - a
  证明: by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]

Depends on / 依赖: Nat.card_Ico, card_Ico, card_map, map_valEmbedding_Ico
-/
lemma card_Ico : #(Ico a b) = b - a := by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]
/--
lemma `card_Ioc` / 引理 `card_Ioc`

English:
lemma card_Ioc
  statement: #(Ioc a b) = b - a
  proof: by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]

中文:
引理 card_Ioc
  结论: #(Ioc a b) = b - a
  证明: by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]

Depends on / 依赖: Nat.card_Ioc, card_Ioc, card_map, map_valEmbedding_Ioc
-/
lemma card_Ioc : #(Ioc a b) = b - a := by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]
/--
lemma `card_Ioo` / 引理 `card_Ioo`

English:
lemma card_Ioo
  statement: #(Ioo a b) = b - a - 1
  proof: by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]

中文:
引理 card_Ioo
  结论: #(Ioo a b) = b - a - 1
  证明: by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]

Depends on / 依赖: Nat.card_Ioo, card_Ioo, card_map, map_valEmbedding_Ioo
-/
lemma card_Ioo : #(Ioo a b) = b - a - 1 := by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]
/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  statement: #(uIcc a b) = (b - a : Int).natAbs + 1
  proof: by
  rw [← Nat.card_uIcc]; rw [← map_valEmbedding_uIcc]; rw [card_map]

@[simp]

中文:
定理 card_uIcc
  结论: #(uIcc a b) = (b - a : 整数).natAbs + 1
  证明: by
  rw [← Nat.card_uIcc]; rw [← map_valEmbedding_uIcc]; rw [card_map]

@[simp]

Depends on / 依赖: Nat.card_uIcc, card_map, card_uIcc, map_valEmbedding_uIcc
-/
theorem card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1 := by
  rw [← Nat.card_uIcc]; rw [← map_valEmbedding_uIcc]; rw [card_map]

@[simp]
/--
theorem `card_Ici` / 定理 `card_Ici`

English:
theorem card_Ici
  statement: #(Ici a) = n - a
  proof: by
  rw [← attachFin_Ico_eq_Ici]; rw [card_attachFin]; rw [Nat.card_Ico]

@[simp]

中文:
定理 card_Ici
  结论: #(Ici a) = n - a
  证明: by
  rw [← attachFin_Ico_eq_Ici]; rw [card_attachFin]; rw [Nat.card_Ico]

@[simp]

Depends on / 依赖: Nat.card_Ico, attachFin_Ico_eq_Ici, card_Ico, card_attachFin
-/
theorem card_Ici : #(Ici a) = n - a := by
  rw [← attachFin_Ico_eq_Ici]; rw [card_attachFin]; rw [Nat.card_Ico]

@[simp]
/--
theorem `card_Ioi` / 定理 `card_Ioi`

English:
theorem card_Ioi
  statement: #(Ioi a) = n - 1 - a
  proof: by
  rw [← card_map]; rw [map_valEmbedding_Ioi]; rw [Nat.card_Ioo]; rw [Nat.sub_right_comm]

@[simp]

中文:
定理 card_Ioi
  结论: #(Ioi a) = n - 1 - a
  证明: by
  rw [← card_map]; rw [map_valEmbedding_Ioi]; rw [Nat.card_Ioo]; rw [Nat.sub_right_comm]

@[simp]

Depends on / 依赖: Nat.card_Ioo, Nat.sub_right_comm, card_Ioo, card_map, map_valEmbedding_Ioi, sub_right_comm
-/
theorem card_Ioi : #(Ioi a) = n - 1 - a := by
  rw [← card_map]; rw [map_valEmbedding_Ioi]; rw [Nat.card_Ioo]; rw [Nat.sub_right_comm]

@[simp]
/--
theorem `card_Iic` / 定理 `card_Iic`

English:
theorem card_Iic
  statement: #(Iic b) = b + 1
  proof: by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]

中文:
定理 card_Iic
  结论: #(Iic b) = b + 1
  证明: by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]

Depends on / 依赖: Nat.card_Iic, card_Iic, card_map, map_valEmbedding_Iic
-/
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
/--
theorem `card_Iio` / 定理 `card_Iio`

English:
theorem card_Iio
  statement: #(Iio b) = b
  proof: by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

中文:
定理 card_Iio
  结论: #(Iio b) = b
  证明: by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

Depends on / 依赖: Nat.card_Iio, card_Iio, card_map, map_valEmbedding_Iio
-/
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

end card

/-! ### Perturbations of endpoints by one -/

/-
Note: the `haveI`s in the statements below are needed for `0` and `1`
to be defined in `Fin n`. One could instead add `[NeZero n]` at the
top of this section, but then this instance would be required to
rewrite using the lemmas.
-/

section pm_one

/--
lemma `Iio_add_one_eq_Iic` / 引理 `Iio_add_one_eq_Iic`

English:
lemma Iio_add_one_eq_Iic
  given: {n : Nat} {b : Fin n} (hb : b + 1 < n)
  proof: b.neZero
    Iio (b + 1) = Iic b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Iio_add_one_eq_Iic
  条件: {n : 自然数} {b : Fin n} (hb : b + 1 < n)
  证明: b.neZero
    Iio (b + 1) = Iic b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: b.neZero, neZero
-/
lemma Iio_add_one_eq_Iic {n : Nat} {b : Fin n} (hb : b + 1 < n) :
    haveI := b.neZero
    Iio (b + 1) = Iic b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

/--
lemma `Iic_sub_one_eq_Iio` / 引理 `Iic_sub_one_eq_Iio`

English:
lemma Iic_sub_one_eq_Iio
  given: {n : Nat} {b : Fin n}
  proof: b.neZero
    (hb : 0 < b) -> Iic (b - 1) = Iio b := by
  grind [= Fin.val_sub_one_of_ne_zero]

中文:
引理 Iic_sub_one_eq_Iio
  条件: {n : 自然数} {b : Fin n}
  证明: b.neZero
    (hb : 0 < b) -> Iic (b - 1) = Iio b := by
  grind [= Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: b.neZero, neZero
-/
lemma Iic_sub_one_eq_Iio {n : Nat} {b : Fin n} :
    haveI := b.neZero
    (hb : 0 < b) -> Iic (b - 1) = Iio b := by
  grind [= Fin.val_sub_one_of_ne_zero]

/--
lemma `Ici_add_one_eq_Ioi` / 引理 `Ici_add_one_eq_Ioi`

English:
lemma Ici_add_one_eq_Ioi
  given: {n : Nat} {a : Fin n} (ha : a + 1 < n)
  proof: a.neZero
    Ici (a + 1) = Ioi a := by
  grind [= Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Ici_add_one_eq_Ioi
  条件: {n : 自然数} {a : Fin n} (ha : a + 1 < n)
  证明: a.neZero
    Ici (a + 1) = Ioi a := by
  grind [= Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: a.neZero, neZero
-/
lemma Ici_add_one_eq_Ioi {n : Nat} {a : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Ici (a + 1) = Ioi a := by
  grind [= Fin.le_def, = Fin.val_add_one_of_lt']

/--
lemma `Ioi_sub_one_eq_Ici` / 引理 `Ioi_sub_one_eq_Ici`

English:
lemma Ioi_sub_one_eq_Ici
  given: {n : Nat} {a : Fin n}
  proof: a.neZero
    (ha : 0 < a) -> Ioi (a - 1) = Ici a := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

中文:
引理 Ioi_sub_one_eq_Ici
  条件: {n : 自然数} {a : Fin n}
  证明: a.neZero
    (ha : 0 < a) -> Ioi (a - 1) = Ici a := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: a.neZero, neZero
-/
lemma Ioi_sub_one_eq_Ici {n : Nat} {a : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) -> Ioi (a - 1) = Ici a := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

/--
lemma `Ioc_sub_one_eq_Icc` / 引理 `Ioc_sub_one_eq_Icc`

English:
lemma Ioc_sub_one_eq_Icc
  given: {n : Nat} {a b : Fin n}
  proof: a.neZero
    (ha : 0 < a) -> Ioc (a - 1) b = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

中文:
引理 Ioc_sub_one_eq_Icc
  条件: {n : 自然数} {a b : Fin n}
  证明: a.neZero
    (ha : 0 < a) -> Ioc (a - 1) b = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: a.neZero, neZero
-/
lemma Ioc_sub_one_eq_Icc {n : Nat} {a b : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) -> Ioc (a - 1) b = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

/--
lemma `Icc_add_one_eq_Ioc` / 引理 `Icc_add_one_eq_Ioc`

English:
lemma Icc_add_one_eq_Ioc
  given: {n : Nat} {a b : Fin n} (ha : a + 1 < n)
  proof: a.neZero
    Icc (a + 1) b = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Icc_add_one_eq_Ioc
  条件: {n : 自然数} {a b : Fin n} (ha : a + 1 < n)
  证明: a.neZero
    Icc (a + 1) b = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: a.neZero, neZero
-/
lemma Icc_add_one_eq_Ioc {n : Nat} {a b : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Icc (a + 1) b = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

/--
lemma `Ioo_sub_one_eq_Ico` / 引理 `Ioo_sub_one_eq_Ico`

English:
lemma Ioo_sub_one_eq_Ico
  given: {n : Nat} {a b : Fin n}
  proof: a.neZero
    (ha : 0 < a) -> Ioo (a - 1) b = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

中文:
引理 Ioo_sub_one_eq_Ico
  条件: {n : 自然数} {a b : Fin n}
  证明: a.neZero
    (ha : 0 < a) -> Ioo (a - 1) b = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: a.neZero, neZero
-/
lemma Ioo_sub_one_eq_Ico {n : Nat} {a b : Fin n} :
    haveI := a.neZero
    (ha : 0 < a) -> Ioo (a - 1) b = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

/--
lemma `Ico_add_one_eq_Ioo` / 引理 `Ico_add_one_eq_Ioo`

English:
lemma Ico_add_one_eq_Ioo
  given: {n : Nat} {a b : Fin n} (ha : a + 1 < n)
  proof: a.neZero
    Ico (a + 1) b = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Ico_add_one_eq_Ioo
  条件: {n : 自然数} {a b : Fin n} (ha : a + 1 < n)
  证明: a.neZero
    Ico (a + 1) b = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: a.neZero, neZero
-/
lemma Ico_add_one_eq_Ioo {n : Nat} {a b : Fin n} (ha : a + 1 < n) :
    haveI := a.neZero
    Ico (a + 1) b = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

/--
lemma `Icc_sub_one_eq_Ico` / 引理 `Icc_sub_one_eq_Ico`

English:
lemma Icc_sub_one_eq_Ico
  given: {n : Nat} {a b : Fin n}
  proof: a.neZero
    (hb : 0 < b) -> Icc a (b - 1) = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

中文:
引理 Icc_sub_one_eq_Ico
  条件: {n : 自然数} {a b : Fin n}
  证明: a.neZero
    (hb : 0 < b) -> Icc a (b - 1) = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: a.neZero, neZero
-/
lemma Icc_sub_one_eq_Ico {n : Nat} {a b : Fin n} :
    haveI := a.neZero
    (hb : 0 < b) -> Icc a (b - 1) = Ico a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

/--
lemma `Ico_add_one_eq_Icc` / 引理 `Ico_add_one_eq_Icc`

English:
lemma Ico_add_one_eq_Icc
  given: {n : Nat} {a b : Fin n} (hb : b + 1 < n)
  proof: a.neZero
    Ico a (b + 1) = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Ico_add_one_eq_Icc
  条件: {n : 自然数} {a b : Fin n} (hb : b + 1 < n)
  证明: a.neZero
    Ico a (b + 1) = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: a.neZero, neZero
-/
lemma Ico_add_one_eq_Icc {n : Nat} {a b : Fin n} (hb : b + 1 < n) :
    haveI := a.neZero
    Ico a (b + 1) = Icc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

/--
lemma `Ioc_sub_one_eq_Ioo` / 引理 `Ioc_sub_one_eq_Ioo`

English:
lemma Ioc_sub_one_eq_Ioo
  given: {n : Nat} {a b : Fin n}
  proof: a.neZero
    (hb : 0 < b) -> Ioc a (b - 1) = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

中文:
引理 Ioc_sub_one_eq_Ioo
  条件: {n : 自然数} {a b : Fin n}
  证明: a.neZero
    (hb : 0 < b) -> Ioc a (b - 1) = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: a.neZero, neZero
-/
lemma Ioc_sub_one_eq_Ioo {n : Nat} {a b : Fin n} :
    haveI := a.neZero
    (hb : 0 < b) -> Ioc a (b - 1) = Ioo a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_sub_one_of_ne_zero]

/--
lemma `Ioo_add_one_eq_Ioc` / 引理 `Ioo_add_one_eq_Ioc`

English:
lemma Ioo_add_one_eq_Ioc
  given: {n : Nat} {a b : Fin n} (hb : b + 1 < n)
  proof: a.neZero
    Ioo a (b + 1) = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

中文:
引理 Ioo_add_one_eq_Ioc
  条件: {n : 自然数} {a b : Fin n} (hb : b + 1 < n)
  证明: a.neZero
    Ioo a (b + 1) = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

Depends on / 依赖: a.neZero, neZero
-/
lemma Ioo_add_one_eq_Ioc {n : Nat} {a b : Fin n} (hb : b + 1 < n) :
    haveI := a.neZero
    Ioo a (b + 1) = Ioc a b := by
  grind [= Fin.lt_def, = Fin.le_def, = Fin.val_add_one_of_lt']

end pm_one

end Fin
