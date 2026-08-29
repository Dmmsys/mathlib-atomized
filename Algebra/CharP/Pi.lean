/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions
-/

public section


universe u v

namespace CharP

/--
Instance `pi` / 实例 `pi`

English:
instance pi
  signature: (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : Nat) [CharP R p]
  body: ⟨fun x =>
    let ⟨i⟩ := hi
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι -> R) = 0 by rw [map_natCast, h],
          fun h => by rw [← map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x, h, map_zero]⟩⟩

中文:
实例 pi
  签名: (ι : 类型u) [hi : 非空 ι] (R : 类型v) [半环 R] (p : 自然数) [特征p R p]
  定义体: ⟨fun x =>
    let ⟨i⟩ := hi
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι -> R) = 0 by rw [map_natCast, h],
          fun h => by rw [← map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x, h, map_zero]⟩⟩

Depends on / 依赖: CharP.cast_eq_zero_iff, Iff.symm, Pi.evalRingHom, cast_eq_zero_iff, evalRingHom, map_natCast, map_zero, symm.trans
-/
instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : Nat) [CharP R p] :
    CharP (ι -> R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι -> R) = 0 by rw [map_natCast, h],
          fun h => by rw [← map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x, h, map_zero]⟩⟩

-- diamonds
/--
Instance `pi'` / 实例 `pi'`

English:
instance pi'
  signature: (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : Nat) [CharP R p]
  body: CharP.pi ι R p

中文:
实例 pi'
  签名: (ι : 类型u) [非空 ι] (R : 类型v) [交换环 R] (p : 自然数) [特征p R p]
  定义体: CharP.pi ι R p

Depends on / 依赖: CharP.pi
-/
instance pi' (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : Nat) [CharP R p] :
    CharP (ι -> R) p :=
  CharP.pi ι R p

end CharP
