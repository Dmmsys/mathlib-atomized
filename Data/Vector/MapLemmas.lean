/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
module

public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Snoc

/-!
  This file establishes a set of normalization lemmas for `map`/`mapAccumr` operations on vectors
-/

public section

variable {α β γ ζ σ σ₁ σ₂ φ : Type*} {n : Nat} {s : σ} {s₁ : σ₁} {s₂ : σ₂}

namespace List
namespace Vector

/-!
## Fold nested `mapAccumr`s into one
-/
section Fold

section Unary
variable (xs : Vector α n) (f₁ : β -> σ₁ -> σ₁ × γ) (f₂ : α -> σ₂ -> σ₂ × β)

@[simp]
/--
theorem `mapAccumr_mapAccumr` / 定理 `mapAccumr_mapAccumr`

English:
theorem mapAccumr_mapAccumr
  proof: (mapAccumr (fun x s =>
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)
      ) xs (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂ <;> simp_all

@[simp]

中文:
定理 mapAccumr_mapAccumr
  证明: (mapAccumr (fun x s =>
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)
      ) xs (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂ <;> simp_all

@[simp]

Depends on / 依赖: mapAccumr
-/
theorem mapAccumr_mapAccumr :
    mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁
    = let m := (mapAccumr (fun x s =>
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)
      ) xs (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr_map` / 定理 `mapAccumr_map`

English:
theorem mapAccumr_map
  given: {s : σ₁} (f₂ : α -> β)
  proof: by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]

中文:
定理 mapAccumr_map
  条件: {s : σ₁} (f₂ : α -> β)
  证明: by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]

Depends on / 依赖: Vector, Vector.revInductionOn, generalizing, revInductionOn
-/
theorem mapAccumr_map {s : σ₁} (f₂ : α -> β) :
    (mapAccumr f₁ (map f₂ xs) s) = (mapAccumr (fun x s => f₁ (f₂ x) s) xs s) := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
/--
theorem `map_mapAccumr` / 定理 `map_mapAccumr`

English:
theorem map_mapAccumr
  given: {s : σ₂} (f₁ : β -> γ)
  proof: by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]

中文:
定理 map_mapAccumr
  条件: {s : σ₂} (f₁ : β -> γ)
  证明: by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]

Depends on / 依赖: r.fst, r.snd
-/
theorem map_mapAccumr {s : σ₂} (f₁ : β -> γ) :
    (map f₁ (mapAccumr f₂ xs s).snd) = (mapAccumr (fun x s =>
        let r := (f₂ x s); (r.fst, f₁ r.snd)
      ) xs s).snd := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (f₁ : β -> γ) (f₂ : α -> β)
  proof: by
  induction xs <;> simp_all

中文:
定理 map_map
  条件: (f₁ : β -> γ) (f₂ : α -> β)
  证明: by
  induction xs <;> simp_all
-/
theorem map_map (f₁ : β -> γ) (f₂ : α -> β) :
    map f₁ (map f₂ xs) = map (fun x => f₁ <| f₂ x) xs := by
  induction xs <;> simp_all

/--
theorem `map_pmap` / 定理 `map_pmap`

English:
theorem map_pmap
  given: {p : α -> Prop} (f₁ : β -> γ) (f₂ : (a : α) -> p a -> β) (H : forall x in xs.toList, p x)
  proof: by
  induction xs <;> simp_all

中文:
定理 map_pmap
  条件: {p : α -> 命题} (f₁ : β -> γ) (f₂ : (a : α) -> p a -> β) (H : 对任意 x in xs.toList, p x)
  证明: by
  induction xs <;> simp_all
-/
theorem map_pmap {p : α -> Prop} (f₁ : β -> γ) (f₂ : (a : α) -> p a -> β) (H : forall x in xs.toList, p x) :
    map f₁ (pmap f₂ xs H) = pmap (fun x hx => f₁ <| f₂ x hx) xs H := by
  induction xs <;> simp_all

/--
theorem `pmap_map` / 定理 `pmap_map`

English:
theorem pmap_map
  statement: {p : β -> Prop} (f₁ : (b : β) -> p b -> γ) (f₂ : α -> β)
  proof: by
  induction xs <;> simp_all

中文:
定理 pmap_map
  结论: {p : β -> 命题} (f₁ : (b : β) -> p b -> γ) (f₂ : α -> β)
  证明: by
  induction xs <;> simp_all
-/
theorem pmap_map {p : β -> Prop} (f₁ : (b : β) -> p b -> γ) (f₂ : α -> β)
    (H : forall x in (xs.map f₂).toList, p x) :
    pmap f₁ (map f₂ xs) H = pmap (fun x hx => f₁ (f₂ x) hx) xs (by simpa using H) := by
  induction xs <;> simp_all

end Unary

section Binary
variable (xs : Vector α n) (ys : Vector β n)

@[simp]
/--
theorem `mapAccumr₂_mapAccumr_left` / 定理 `mapAccumr₂_mapAccumr_left`

English:
theorem mapAccumr₂_mapAccumr_left
  given: (f₁ : γ -> β -> σ₁ -> σ₁ × ζ) (f₂ : α -> σ₂ -> σ₂ × γ)
  proof: (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x s.snd
          let r₁ := f₁ r₂.snd y s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]

中文:
定理 mapAccumr₂_mapAccumr_left
  条件: (f₁ : γ -> β -> σ₁ -> σ₁ × ζ) (f₂ : α -> σ₂ -> σ₂ × γ)
  证明: (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x s.snd
          let r₁ := f₁ r₂.snd y s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
-/
theorem mapAccumr₂_mapAccumr_left (f₁ : γ -> β -> σ₁ -> σ₁ × ζ) (f₂ : α -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr f₂ xs s₂).snd ys s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x s.snd
          let r₁ := f₁ r₂.snd y s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `map₂_map_left` / 定理 `map₂_map_left`

English:
theorem map₂_map_left
  given: (f₁ : γ -> β -> ζ) (f₂ : α -> γ)
  proof: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

中文:
定理 map₂_map_left
  条件: (f₁ : γ -> β -> ζ) (f₂ : α -> γ)
  证明: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

Depends on / 依赖: Vector, Vector.revInductionOn
-/
theorem map₂_map_left (f₁ : γ -> β -> ζ) (f₂ : α -> γ) :
    map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_mapAccumr_right` / 定理 `mapAccumr₂_mapAccumr_right`

English:
theorem mapAccumr₂_mapAccumr_right
  given: (f₁ : α -> γ -> σ₁ -> σ₁ × ζ) (f₂ : β -> σ₂ -> σ₂ × γ)
  proof: (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ y s.snd
          let r₁ := f₁ x r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]

中文:
定理 mapAccumr₂_mapAccumr_right
  条件: (f₁ : α -> γ -> σ₁ -> σ₁ × ζ) (f₂ : β -> σ₂ -> σ₂ × γ)
  证明: (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ y s.snd
          let r₁ := f₁ x r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
-/
theorem mapAccumr₂_mapAccumr_right (f₁ : α -> γ -> σ₁ -> σ₁ × ζ) (f₂ : β -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr f₂ ys s₂).snd s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ y s.snd
          let r₁ := f₁ x r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `map₂_map_right` / 定理 `map₂_map_right`

English:
theorem map₂_map_right
  given: (f₁ : α -> γ -> ζ) (f₂ : β -> γ)
  proof: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

中文:
定理 map₂_map_right
  条件: (f₁ : α -> γ -> ζ) (f₂ : β -> γ)
  证明: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

Depends on / 依赖: Vector, Vector.revInductionOn
-/
theorem map₂_map_right (f₁ : α -> γ -> ζ) (f₂ : β -> γ) :
    map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr_mapAccumr₂` / 定理 `mapAccumr_mapAccumr₂`

English:
theorem mapAccumr_mapAccumr₂
  given: (f₁ : γ -> σ₁ -> σ₁ × ζ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  proof: mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂)
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]

中文:
定理 mapAccumr_mapAccumr₂
  条件: (f₁ : γ -> σ₁ -> σ₁ × ζ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  证明: mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂)
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
-/
theorem mapAccumr_mapAccumr₂ (f₁ : γ -> σ₁ -> σ₁ × ζ) (f₂ : α -> β -> σ₂ -> σ₂ × γ) :
    (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂)
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `map_map₂` / 定理 `map_map₂`

English:
theorem map_map₂
  given: (f₁ : γ -> ζ) (f₂ : α -> β -> γ)
  proof: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

中文:
定理 map_map₂
  条件: (f₁ : γ -> ζ) (f₂ : α -> β -> γ)
  证明: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]

Depends on / 依赖: Vector, Vector.revInductionOn
-/
theorem map_map₂ (f₁ : γ -> ζ) (f₂ : α -> β -> γ) :
    map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_mapAccumr₂_left_left` / 定理 `mapAccumr₂_mapAccumr₂_left_left`

English:
theorem mapAccumr₂_mapAccumr₂_left_left
  given: (f₁ : γ -> α -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  proof: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_

中文:
定理 mapAccumr₂_mapAccumr₂_left_left
  条件: (f₁ : γ -> α -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  证明: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_
-/
theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ -> α -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd xs s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_mapAccumr₂_left_right` / 定理 `mapAccumr₂_mapAccumr₂_left_right`

English:
theorem mapAccumr₂_mapAccumr₂_left_right
  proof: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_

中文:
定理 mapAccumr₂_mapAccumr₂_left_right
  证明: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_
-/
theorem mapAccumr₂_mapAccumr₂_left_right
    (f₁ : γ -> β -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd ys s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_mapAccumr₂_right_left` / 定理 `mapAccumr₂_mapAccumr₂_right_left`

English:
theorem mapAccumr₂_mapAccumr₂_right_left
  given: (f₁ : α -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  proof: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_

中文:
定理 mapAccumr₂_mapAccumr₂_right_left
  条件: (f₁ : α -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  证明: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_
-/
theorem mapAccumr₂_mapAccumr₂_right_left (f₁ : α -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_mapAccumr₂_right_right` / 定理 `mapAccumr₂_mapAccumr₂_right_right`

English:
theorem mapAccumr₂_mapAccumr₂_right_right
  given: (f₁ : β -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  proof: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_

中文:
定理 mapAccumr₂_mapAccumr₂_right_right
  条件: (f₁ : β -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ)
  证明: mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_
-/
theorem mapAccumr₂_mapAccumr₂_right_right (f₁ : β -> γ -> σ₁ -> σ₁ × φ) (f₂ : α -> β -> σ₂ -> σ₂ × γ) :
    (mapAccumr₂ f₁ ys (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

end Binary

end Fold

/-!
## Bisimulations
We can prove two applications of `mapAccumr` equal by providing a bisimulation relation that relates
the initial states.

That is, by providing a relation `R : σ₁ → σ₁ → Prop` such that `R s₁ s₂` implies that `R` also
relates any pair of states reachable by applying `f₁` to `s₁` and `f₂` to `s₂`, with any possible
input values.
-/

section Bisim
variable {xs : Vector α n}

/--
theorem `mapAccumr_bisim` / 定理 `mapAccumr_bisim`

English:
theorem mapAccumr_bisim
  statement: {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
  proof: by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih hR, true_and]
    congr 1

中文:
定理 mapAccumr_bisim
  结论: {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
  证明: by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih hR, true_and]
    congr 1

Depends on / 依赖: Vector, Vector.revInductionOn, generalizing, mapAccumr_snoc, revInductionOn, true_and
-/
theorem mapAccumr_bisim {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
    (R : σ₁ -> σ₂ -> Prop) (h₀ : R s₁ s₂)
    (hR : forall {s q} a, R s q -> R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    R (mapAccumr f₁ xs s₁).fst (mapAccumr f₂ xs s₂).fst
    ∧ (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih hR, true_and]
    congr 1

/--
theorem `mapAccumr_bisim_tail` / 定理 `mapAccumr_bisim_tail`

English:
theorem mapAccumr_bisim_tail
  statement: {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
  proof: by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr_bisim R h₀ hR).2

中文:
定理 mapAccumr_bisim_tail
  结论: {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
  证明: by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr_bisim R h₀ hR).2

Depends on / 依赖: mapAccumr_bisim
-/
theorem mapAccumr_bisim_tail {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
    (h : exists R : σ₁ -> σ₂ -> Prop, R s₁ s₂ ∧
      forall {s q} a, R s q -> R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr_bisim R h₀ hR).2

/--
theorem `mapAccumr₂_bisim` / 定理 `mapAccumr₂_bisim`

English:
theorem mapAccumr₂_bisim
  statement: {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
  proof: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih hR, true_and]
    congr 1

中文:
定理 mapAccumr₂_bisim
  结论: {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
  证明: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih hR, true_and]
    congr 1

Depends on / 依赖: Vector, Vector.revInductionOn, generalizing, true_and
-/
theorem mapAccumr₂_bisim {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
    {f₂ : α -> β -> σ₂ -> σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (R : σ₁ -> σ₂ -> Prop) (h₀ : R s₁ s₂)
    (hR : forall {s q} a b, R s q -> R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    R (mapAccumr₂ f₁ xs ys s₁).1 (mapAccumr₂ f₂ xs ys s₂).1
    ∧ (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih hR, true_and]
    congr 1

/--
theorem `mapAccumr₂_bisim_tail` / 定理 `mapAccumr₂_bisim_tail`

English:
theorem mapAccumr₂_bisim_tail
  statement: {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
  proof: by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr₂_bisim R h₀ hR).2

中文:
定理 mapAccumr₂_bisim_tail
  结论: {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
  证明: by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr₂_bisim R h₀ hR).2
-/
theorem mapAccumr₂_bisim_tail {ys : Vector β n} {f₁ : α -> β -> σ₁ -> σ₁ × γ}
    {f₂ : α -> β -> σ₂ -> σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (h : exists R : σ₁ -> σ₂ -> Prop, R s₁ s₂ ∧
      forall {s q} a b, R s q -> R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr₂_bisim R h₀ hR).2

end Bisim

/-!
## Redundant state optimization

The following section are collection of rewrites to simplify, or even get rid, redundant
accumulation state
-/
section RedundantState
variable {xs : Vector α n} {ys : Vector β n}

/--
theorem `map_eq_mapAccumr` / 定理 `map_eq_mapAccumr`

English:
theorem map_eq_mapAccumr
  given: {f : α -> β}
  proof: by
  induction xs using Vector.revInductionOn <;> simp_all

中文:
定理 map_eq_mapAccumr
  条件: {f : α -> β}
  证明: by
  induction xs using Vector.revInductionOn <;> simp_all
-/
protected theorem map_eq_mapAccumr {f : α -> β} :
    map f xs = (mapAccumr (fun x (_ : Unit) => ((), f x)) xs ()).snd := by
  induction xs using Vector.revInductionOn <;> simp_all

/--
theorem `mapAccumr_eq_map` / 定理 `mapAccumr_eq_map`

English:
theorem mapAccumr_eq_map
  statement: {f : α -> σ -> σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ in S)
  proof: by
  rw [Vector.map_eq_mapAccumr]
  apply mapAccumr_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a h => ⟨closure a s h, out a s s₀ h h₀⟩

中文:
定理 mapAccumr_eq_map
  结论: {f : α -> σ -> σ × β} {s₀ : σ} (S : 集合 σ) (h₀ : s₀ in S)
  证明: by
  rw [Vector.map_eq_mapAccumr]
  apply mapAccumr_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a h => ⟨closure a s h, out a s s₀ h h₀⟩

Depends on / 依赖: Vector, Vector.map_eq_mapAccumr, closure, mapAccumr_bisim_tail, map_eq_mapAccumr
-/
theorem mapAccumr_eq_map {f : α -> σ -> σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ in S)
    (closure : forall a s, s in S -> (f a s).1 in S)
    (out : forall a s s', s in S -> s' in S -> (f a s).2 = (f a s').2) :
    (mapAccumr f xs s₀).snd = map (f · s₀ |>.snd) xs := by
  rw [Vector.map_eq_mapAccumr]
  apply mapAccumr_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a h => ⟨closure a s h, out a s s₀ h h₀⟩

/--
theorem `map₂_eq_mapAccumr₂` / 定理 `map₂_eq_mapAccumr₂`

English:
theorem map₂_eq_mapAccumr₂
  given: {f : α -> β -> γ}
  proof: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

中文:
定理 map₂_eq_mapAccumr₂
  条件: {f : α -> β -> γ}
  证明: by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all
-/
protected theorem map₂_eq_mapAccumr₂ {f : α -> β -> γ} :
    map₂ f xs ys = (mapAccumr₂ (fun x y (_ : Unit) => ((), f x y)) xs ys ()).snd := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

/--
theorem `mapAccumr₂_eq_map₂` / 定理 `mapAccumr₂_eq_map₂`

English:
theorem mapAccumr₂_eq_map₂
  statement: {f : α -> β -> σ -> σ × γ} {s₀ : σ} (S : Set σ) (h₀ : s₀ in S)
  proof: by
  rw [Vector.map₂_eq_mapAccumr₂]
  apply mapAccumr₂_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a b h => ⟨closure a b s h, out a b s s₀ h h₀⟩

中文:
定理 mapAccumr₂_eq_map₂
  结论: {f : α -> β -> σ -> σ × γ} {s₀ : σ} (S : 集合 σ) (h₀ : s₀ in S)
  证明: by
  rw [Vector.map₂_eq_mapAccumr₂]
  apply mapAccumr₂_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a b h => ⟨closure a b s h, out a b s s₀ h h₀⟩

Depends on / 依赖: Vector, Vector.map, closure
-/
theorem mapAccumr₂_eq_map₂ {f : α -> β -> σ -> σ × γ} {s₀ : σ} (S : Set σ) (h₀ : s₀ in S)
    (closure : forall a b s, s in S -> (f a b s).1 in S)
    (out : forall a b s s', s in S -> s' in S -> (f a b s).2 = (f a b s').2) :
    (mapAccumr₂ f xs ys s₀).snd = map₂ (f · · s₀ |>.snd) xs ys := by
  rw [Vector.map₂_eq_mapAccumr₂]
  apply mapAccumr₂_bisim_tail
  use fun s _ => s in S, h₀
  exact @fun s _q a b h => ⟨closure a b s h, out a b s s₀ h h₀⟩

/--
If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
for all possible input bits, then the state is redundant and can be optimized out.
-/
@[simp]
/--
theorem `mapAccumr_eq_map_of_constant_state` / 定理 `mapAccumr_eq_map_of_constant_state`

English:
theorem mapAccumr_eq_map_of_constant_state
  given: (f : α -> σ -> σ × β) (s : σ) (h : forall a, (f a s).fst = s)
  proof: by
  induction xs using revInductionOn <;> simp_all

中文:
定理 mapAccumr_eq_map_of_constant_state
  条件: (f : α -> σ -> σ × β) (s : σ) (h : 对任意 a, (f a s).fst = s)
  证明: by
  induction xs using revInductionOn <;> simp_all

Depends on / 依赖: revInductionOn
-/
theorem mapAccumr_eq_map_of_constant_state (f : α -> σ -> σ × β) (s : σ) (h : forall a, (f a s).fst = s) :
    mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
  induction xs using revInductionOn <;> simp_all

/--
If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
for all possible input bits, then the state is redundant and can be optimized out.
-/
@[simp]
/--
theorem `mapAccumr₂_eq_map₂_of_constant_state` / 定理 `mapAccumr₂_eq_map₂_of_constant_state`

English:
theorem mapAccumr₂_eq_map₂_of_constant_state
  statement: (f : α -> β -> σ -> σ × γ) (s : σ)
  proof: by
  induction xs, ys using revInductionOn₂ <;> simp_all

中文:
定理 mapAccumr₂_eq_map₂_of_constant_state
  结论: (f : α -> β -> σ -> σ × γ) (s : σ)
  证明: by
  induction xs, ys using revInductionOn₂ <;> simp_all
-/
theorem mapAccumr₂_eq_map₂_of_constant_state (f : α -> β -> σ -> σ × γ) (s : σ)
    (h : forall a b, (f a b s).fst = s) :
    mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
  induction xs, ys using revInductionOn₂ <;> simp_all

/--
If an accumulation function `f`, produces the same output bits regardless of accumulation state,
then the state is redundant and can be optimized out.
-/
@[simp]
/--
theorem `mapAccumr_eq_map_of_unused_state` / 定理 `mapAccumr_eq_map_of_unused_state`

English:
theorem mapAccumr_eq_map_of_unused_state
  statement: (f : α -> σ -> σ × β) (f' : α -> β) (s : σ)
  proof: by
  rw [mapAccumr_eq_map Set.univ (Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    (fun a s s' _ _ => by rw [h]; rw [h])]
  simp_all

中文:
定理 mapAccumr_eq_map_of_unused_state
  结论: (f : α -> σ -> σ × β) (f' : α -> β) (s : σ)
  证明: by
  rw [mapAccumr_eq_map Set.univ (Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    (fun a s s' _ _ => by rw [h]; rw [h])]
  simp_all

Depends on / 依赖: Set.mem_univ, Set.univ, mapAccumr_eq_map, mem_univ
-/
theorem mapAccumr_eq_map_of_unused_state (f : α -> σ -> σ × β) (f' : α -> β) (s : σ)
    (h : forall a s, (f a s).snd = f' a) :
    (mapAccumr f xs s).snd = (map f' xs) := by
  rw [mapAccumr_eq_map Set.univ (Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    (fun a s s' _ _ => by rw [h]; rw [h])]
  simp_all

/--
If an accumulation function `f`, produces the same output bits regardless of accumulation state,
then the state is redundant and can be optimized out.
-/
@[simp]
/--
theorem `mapAccumr₂_eq_map₂_of_unused_state` / 定理 `mapAccumr₂_eq_map₂_of_unused_state`

English:
theorem mapAccumr₂_eq_map₂_of_unused_state
  statement: (f : α -> β -> σ -> σ × γ) (f' : α -> β -> γ) (s : σ)
  proof: mapAccumr₂_eq_map₂ .univ (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
    (fun a b s s' _ _ => by rw [h, h])

中文:
定理 mapAccumr₂_eq_map₂_of_unused_state
  结论: (f : α -> β -> σ -> σ × γ) (f' : α -> β -> γ) (s : σ)
  证明: mapAccumr₂_eq_map₂ .univ (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
    (fun a b s s' _ _ => by rw [h, h])

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mapAccumr₂_eq_map₂_of_unused_state (f : α -> β -> σ -> σ × γ) (f' : α -> β -> γ) (s : σ)
    (h : forall a b s, (f a b s).snd = f' a b) :
    (mapAccumr₂ f xs ys s).snd = (map₂ (fun x y => (f x y s).snd) xs ys) :=
  mapAccumr₂_eq_map₂ .univ (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
    (fun a b s s' _ _ => by rw [h, h])

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
pair, then we can simplify to just a single element of state.
-/
@[simp]
/--
theorem `mapAccumr_redundant_pair` / 定理 `mapAccumr_redundant_pair`

English:
theorem mapAccumr_redundant_pair
  statement: (f : α -> (σ × σ) -> (σ × σ) × β)
  proof: mapAccumr_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

中文:
定理 mapAccumr_redundant_pair
  结论: (f : α -> (σ × σ) -> (σ × σ) × β)
  证明: mapAccumr_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

Depends on / 依赖: mapAccumr_bisim_tail
-/
theorem mapAccumr_redundant_pair (f : α -> (σ × σ) -> (σ × σ) × β)
    (h : forall x s, (f x (s, s)).fst.fst = (f x (s, s)).fst.snd) :
    (mapAccumr f xs (s, s)).snd = (mapAccumr (fun x (s : σ) =>
      (f x (s, s) |>.fst.fst, f x (s, s) |>.snd)
    ) xs s).snd :=
mapAccumr_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
pair, then we can simplify to just a single element of state.
-/
@[simp]
/--
theorem `mapAccumr₂_redundant_pair` / 定理 `mapAccumr₂_redundant_pair`

English:
theorem mapAccumr₂_redundant_pair
  statement: (f : α -> β -> (σ × σ) -> (σ × σ) × γ)
  proof: mapAccumr₂_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

中文:
定理 mapAccumr₂_redundant_pair
  结论: (f : α -> β -> (σ × σ) -> (σ × σ) × γ)
  证明: mapAccumr₂_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all
-/
theorem mapAccumr₂_redundant_pair (f : α -> β -> (σ × σ) -> (σ × σ) × γ)
    (h : forall x y s, let s' := (f x y (s, s)).fst; s'.fst = s'.snd) :
    (mapAccumr₂ f xs ys (s, s)).snd = (mapAccumr₂ (fun x y (s : σ) =>
      (f x y (s, s) |>.fst.fst, f x y (s, s) |>.snd)
    ) xs ys s).snd :=
mapAccumr₂_bisim_tail by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

end RedundantState

/-!
## Unused input optimizations
-/
section UnusedInput
variable {xs : Vector α n} {ys : Vector β n}

/--
If `f` returns the same output and next state for every value of it's first argument, then
`xs : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
@[simp]
/--
theorem `mapAccumr₂_unused_input_left` / 定理 `mapAccumr₂_unused_input_left`

English:
theorem mapAccumr₂_unused_input_left
  statement: (f : α -> β -> σ -> σ × γ) (f' : β -> σ -> σ × γ)
  proof: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

中文:
定理 mapAccumr₂_unused_input_left
  结论: (f : α -> β -> σ -> σ × γ) (f' : β -> σ -> σ × γ)
  证明: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

Depends on / 依赖: Vector, Vector.revInductionOn, generalizing
-/
theorem mapAccumr₂_unused_input_left (f : α -> β -> σ -> σ × γ) (f' : β -> σ -> σ × γ)
    (h : forall a b s, f a b s = f' b s) :
    mapAccumr₂ f xs ys s = mapAccumr f' ys s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

/--
If `f` returns the same output and next state for every value of it's second argument, then
`ys : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
@[simp]
/--
theorem `mapAccumr₂_unused_input_right` / 定理 `mapAccumr₂_unused_input_right`

English:
theorem mapAccumr₂_unused_input_right
  statement: (f : α -> β -> σ -> σ × γ) (f' : α -> σ -> σ × γ)
  proof: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

中文:
定理 mapAccumr₂_unused_input_right
  结论: (f : α -> β -> σ -> σ × γ) (f' : α -> σ -> σ × γ)
  证明: by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

Depends on / 依赖: Vector, Vector.revInductionOn, generalizing
-/
theorem mapAccumr₂_unused_input_right (f : α -> β -> σ -> σ × γ) (f' : α -> σ -> σ × γ)
    (h : forall a b s, f a b s = f' a s) :
    mapAccumr₂ f xs ys s = mapAccumr f' xs s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

end UnusedInput

/-!
## Commutativity
-/
section Comm
variable (xs ys : Vector α n)

/--
theorem `map₂_comm` / 定理 `map₂_comm`

English:
theorem map₂_comm
  given: (f : α -> α -> β) (comm : forall a₁ a₂, f a₁ a₂ = f a₂ a₁)
  proof: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

中文:
定理 map₂_comm
  条件: (f : α -> α -> β) (comm : 对任意 a₁ a₂, f a₁ a₂ = f a₂ a₁)
  证明: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

Depends on / 依赖: Vector, Vector.inductionOn
-/
theorem map₂_comm (f : α -> α -> β) (comm : forall a₁ a₂, f a₁ a₂ = f a₂ a₁) :
    map₂ f xs ys = map₂ f ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

/--
theorem `mapAccumr₂_comm` / 定理 `mapAccumr₂_comm`

English:
theorem mapAccumr₂_comm
  given: (f : α -> α -> σ -> σ × γ) (comm : forall a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s)
  proof: by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all

中文:
定理 mapAccumr₂_comm
  条件: (f : α -> α -> σ -> σ × γ) (comm : 对任意 a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s)
  证明: by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all

Depends on / 依赖: Vector, Vector.inductionOn, generalizing
-/
theorem mapAccumr₂_comm (f : α -> α -> σ -> σ × γ) (comm : forall a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s) :
    mapAccumr₂ f xs ys s = mapAccumr₂ f ys xs s := by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all

end Comm

/-!
## Argument Flipping
-/
section Flip
variable (xs : Vector α n) (ys : Vector β n)

/--
theorem `map₂_flip` / 定理 `map₂_flip`

English:
theorem map₂_flip
  given: (f : α -> β -> γ)
  proof: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

中文:
定理 map₂_flip
  条件: (f : α -> β -> γ)
  证明: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

Depends on / 依赖: Vector, Vector.inductionOn
-/
theorem map₂_flip (f : α -> β -> γ) :
    map₂ f xs ys = map₂ (flip f) ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

/--
theorem `mapAccumr₂_flip` / 定理 `mapAccumr₂_flip`

English:
theorem mapAccumr₂_flip
  given: (f : α -> β -> σ -> σ × γ)
  proof: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

中文:
定理 mapAccumr₂_flip
  条件: (f : α -> β -> σ -> σ × γ)
  证明: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

Depends on / 依赖: Vector, Vector.inductionOn
-/
theorem mapAccumr₂_flip (f : α -> β -> σ -> σ × γ) :
    mapAccumr₂ f xs ys s = mapAccumr₂ (flip f) ys xs s := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

end Flip

end Vector

end List
