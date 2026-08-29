/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!

# Bézout rings

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notable examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `IsBezout.iff_span_pair_isPrincipal`: It suffices to verify every `span {x, y}` is principal.
- `IsBezout.TFAE`: For a Bézout domain, Noetherian ↔ PID ↔ UFD ↔ ACCP

-/

public section


universe u v

variable {R : Type u} [CommRing R]

namespace IsBezout

/--
theorem `iff_span_pair_isPrincipal` / 定理 `iff_span_pair_isPrincipal`

English:
theorem iff_span_pair_isPrincipal
  proof: by
  constructor
  · intro H x y; infer_instance
  · intro H
    constructor
    apply Submodule.fg_induction
    · exact fun _ => ⟨⟨_, rfl⟩⟩
    · rintro _ _ _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
      rw [← Submodule.span_insert]
      exact H _ _

中文:
定理 iff_span_pair_isPrincipal
  证明: by
  constructor
  · intro H x y; infer_instance
  · intro H
    constructor
    apply Submodule.fg_induction
    · exact fun _ => ⟨⟨_, rfl⟩⟩
    · rintro _ _ _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
      rw [← Submodule.span_insert]
      exact H _ _

Depends on / 依赖: Submodule, Submodule.fg_induction, Submodule.span_insert, fg_induction, infer_instance, span_insert
-/
theorem iff_span_pair_isPrincipal :
    IsBezout R ↔ forall x y : R, (Ideal.span {x, y} : Ideal R).IsPrincipal := by
  constructor
  · intro H x y; infer_instance
  · intro H
    constructor
    apply Submodule.fg_induction
    · exact fun _ => ⟨⟨_, rfl⟩⟩
    · rintro _ _ _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
      rw [← Submodule.span_insert]
      exact H _ _

/--
theorem `_root_.Function.Surjective.isBezout` / 定理 `_root_.Function.Surjective.isBezout`

English:
theorem _root_.Function.Surjective.isBezout
  statement: {S : Type v} [CommRing S] (f : R ->+* S)
  proof: by
  rw [iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]

中文:
定理 _root_.函数.满射.isBezout
  结论: {S : 类型v} [交换环 S] (f : R ->+* S)
  证明: by
  rw [iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]

Depends on / 依赖: Ideal.map, Ideal.map_span, Ideal.span, Set.image_insert_eq, Set.image_singleton, iff_span_pair_isPrincipal, image_insert_eq, image_singleton, map_span, span_gcd
-/
theorem _root_.Function.Surjective.isBezout {S : Type v} [CommRing S] (f : R ->+* S)
    (hf : Function.Surjective f) [IsBezout R] : IsBezout S := by
  rw [iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `TFAE` / 定理 `TFAE`

English:
theorem TFAE
  given: [IsBezout R] [IsDomain R]
  proof: by
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 2 -> 3
  | _ => inferInstance
  tfae_have 3 -> 4
  | _ => inferInstance
  tfae_have 4 -> 1
  | ⟨h⟩ => by
    rw [isNoetherianRing_iff]; rw [isNoetherian_iff_fg_wellFounded]
    refine ⟨RelEmbedding.wellFounded ?_ h⟩
    have : forall I : { J :

中文:
定理 TFAE
  条件: [是Bezout R] [是整环 R]
  证明: by
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 2 -> 3
  | _ => inferInstance
  tfae_have 3 -> 4
  | _ => inferInstance
  tfae_have 4 -> 1
  | ⟨h⟩ => by
    rw [isNoetherianRing_iff]; rw [isNoetherian_iff_fg_wellFounded]
    refine ⟨RelEmbedding.wellFounded ?_ h⟩
    have : forall I : { J :

Depends on / 依赖: Ideal.span, IsBezout, IsBezout.isPrincipal_of_FG, J.FG, RelEmbedding, RelEmbedding.wellFounded, isNoetherianRing_iff, isNoetherian_iff_fg_wellFounded, isPrincipal_of_FG, map_rel_iff, tfae_have, wellFounded
-/
theorem TFAE [IsBezout R] [IsDomain R] :
    List.TFAE
    [IsNoetherianRing R, IsPrincipalIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R] := by
  tfae_have 1 -> 2
  | _ => inferInstance
  tfae_have 2 -> 3
  | _ => inferInstance
  tfae_have 3 -> 4
  | _ => inferInstance
  tfae_have 4 -> 1
  | ⟨h⟩ => by
    rw [isNoetherianRing_iff]; rw [isNoetherian_iff_fg_wellFounded]
    refine ⟨RelEmbedding.wellFounded ?_ h⟩
    have : forall I : { J : Ideal R // J.FG }, exists x : R, (I : Ideal R) = Ideal.span {x} :=
      fun ⟨I, hI⟩ => (IsBezout.isPrincipal_of_FG I hI).1
    choose f hf using this
    exact
      { toFun := f
        inj' := fun x y e => by ext1; rw [hf, hf, e]
        map_rel_iff' := by
          dsimp
          intro a b
          rw [← Ideal.span_singleton_lt_span_singleton]; rw [← hf]; rw [← hf]
          rfl }
  tfae_finish

end IsBezout
