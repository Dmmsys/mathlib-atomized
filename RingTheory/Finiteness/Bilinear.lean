/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Finitely generated submodules and bilinear maps

-/

public section

open Function (Surjective)

namespace Submodule

section Map₂

variable {R M N P : Type*}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]

/--
theorem `FG.map₂` / 定理 `FG.map₂`

English:
theorem FG.map₂
  statement: (f : M ->ₗ[R] N ->ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
  proof: let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

中文:
定理 FG.map₂
  结论: (f : M ->ₗ[R] N ->ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
  证明: let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

Depends on / 依赖: Set.image2, fg_def, hfm.image2, image2
-/
theorem FG.map₂ (f : M ->ₗ[R] N ->ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
    (hq : q.FG) : (map₂ f p q).FG :=
  let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

end Map₂

end Submodule
