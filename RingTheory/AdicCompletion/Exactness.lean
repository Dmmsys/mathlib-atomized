/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Filtration

/-!
# Exactness of adic completion

In this file we establish exactness properties of adic completions. In particular we show:

## Main results

- `AdicCompletion.map_surjective`: Adic completion preserves surjectivity.
- `AdicCompletion.map_injective`: Adic completion preserves injectivity
  of maps between finite modules over a Noetherian ring.
- `AdicCompletion.map_exact`: Over a Noetherian ring adic completion is exact on finite
  modules.

## Implementation details

All results are proven directly without using Mittag-Leffler systems.

-/

public section

universe u v w t

open LinearMap

namespace AdicCompletion

variable {R : Type u} [CommRing R] {I : Ideal R}

section Surjectivity

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

variable {f : M ->ₗ[R] N}

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mapPreimageDelta (hf : Function.Surjective f) (x : AdicCauchySequence I N)
  body: have h : f (yₙ - y) in Submodule.map f (I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [LinearMap.range_eq_top.2 hf]; rw [map_sub]; rw [hyₙ]; rw [hy]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]; rw [← SModEq.sub_mem]
    exact AdicCauchySequence.mk_eq_mk (

中文:
定义 noncomputable
  签名: def mapPreimageDelta (hf : Function.Surjective f) (x : AdicCauchySequence I N)
  定义体: have h : f (yₙ - y) in Submodule.map f (I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [LinearMap.range_eq_top.2 hf]; rw [map_sub]; rw [hyₙ]; rw [hy]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]; rw [← SModEq.sub_mem]
    exact AdicCauchySequence.mk_eq_mk (
-/
private noncomputable def mapPreimageDelta (hf : Function.Surjective f) (x : AdicCauchySequence I N)
    {n : Nat} {y yₙ : M} (hy : f y = x (n + 1)) (hyₙ : f yₙ = x n) :
    {d : (I ^ n • ⊤ : Submodule R M) | f d = f (yₙ - y) } :=
  have h : f (yₙ - y) in Submodule.map f (I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; rw [Submodule.map_top]; rw [LinearMap.range_eq_top.2 hf]; rw [map_sub]; rw [hyₙ]; rw [hy]; rw [← Submodule.neg_mem_iff]; rw [neg_sub]; rw [← SModEq.sub_mem]
    exact AdicCauchySequence.mk_eq_mk (Nat.le_succ n) x
  ⟨⟨h.choose, h.choose_spec.1⟩, h.choose_spec.2⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mapPreimage (hf : Function.Surjective f) (x : AdicCauchySequence I N)
  body: (hf (x (n + 1))).choose
      have hy := (hf (x (n + 1))).choose_spec
      let ⟨yₙ, (hyₙ : f yₙ = x n)⟩ := mapPreimage hf x n
      let ⟨⟨d, _⟩, (p : f d = f (yₙ - y))⟩ := mapPreimageDelta hf x hy hyₙ
      ⟨yₙ - d, by simpa [p]⟩

中文:
定义 noncomputable
  签名: def mapPreimage (hf : Function.Surjective f) (x : AdicCauchySequence I N)
  定义体: (hf (x (n + 1))).choose
      have hy := (hf (x (n + 1))).choose_spec
      let ⟨yₙ, (hyₙ : f yₙ = x n)⟩ := mapPreimage hf x n
      let ⟨⟨d, _⟩, (p : f d = f (yₙ - y))⟩ := mapPreimageDelta hf x hy hyₙ
      ⟨yₙ - d, by simpa [p]⟩
-/
private noncomputable def mapPreimage (hf : Function.Surjective f) (x : AdicCauchySequence I N) :
    (n : Nat) -> f ⁻¹' {x n}
  | .zero => ⟨(hf (x 0)).choose, (hf (x 0)).choose_spec⟩
  | .succ n =>
      let y := (hf (x (n + 1))).choose
      have hy := (hf (x (n + 1))).choose_spec
      let ⟨yₙ, (hyₙ : f yₙ = x n)⟩ := mapPreimage hf x n
      let ⟨⟨d, _⟩, (p : f d = f (yₙ - y))⟩ := mapPreimageDelta hf x hy hyₙ
      ⟨yₙ - d, by simpa [p]⟩

variable (I) in
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (hf : Function.Surjective f)
  statement: Function.Surjective (map I f)
  proof: fun y => by
  apply AdicCompletion.induction_on I N y (fun b => ?_)
  let a := mapPreimage hf b
  refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n => (a n : M)) ?_), ?_⟩
  · refine fun n => SModEq.symm ?_
    simp only [SModEq, mapPreimage, Submodule.Quotient.mk_sub,
      sub_eq_self

中文:
定理 map_surjective
  条件: (hf : Function.Surjective f)
  结论: Function.Surjective (map I f)
  证明: fun y => by
  apply AdicCompletion.induction_on I N y (fun b => ?_)
  let a := mapPreimage hf b
  refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n => (a n : M)) ?_), ?_⟩
  · refine fun n => SModEq.symm ?_
    simp only [SModEq, mapPreimage, Submodule.Quotient.mk_sub,
      sub_eq_self

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.mk, AdicCompletion, AdicCompletion.induction_on, AdicCompletion.mk, Quotient, SModEq, SModEq.symm, SetLike, SetLike.coe_mem, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, _root_, _root_.AdicCompletion.ext, coe_mem, induction_on, mapPreimage, mk_eq_zero, mk_sub
-/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map I f) := fun y => by
  apply AdicCompletion.induction_on I N y (fun b => ?_)
  let a := mapPreimage hf b
  refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n => (a n : M)) ?_), ?_⟩
  · refine fun n => SModEq.symm ?_
    simp only [SModEq, mapPreimage, Submodule.Quotient.mk_sub,
      sub_eq_self, Submodule.Quotient.mk_eq_zero, SetLike.coe_mem, a]
  · exact _root_.AdicCompletion.ext fun n => congrArg _ ((a n).property)

end Surjectivity

variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
variable {P : Type u} [AddCommGroup P] [Module R P]

section Injectivity

variable [IsNoetherianRing R] [Module.Finite R N] (I)

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : M ->ₗ[R] N} (hf : Function.Injective f)
  proof: by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a => ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ => ⟨n + k, by lia, n, by lia, ?_⟩⟩
  rw [← 

中文:
定理 map_injective
  条件: {f : M ->ₗ[R] N} (hf : Function.Injective f)
  证明: by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a => ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ => ⟨n + k, by lia, n, by lia, ?_⟩⟩
  rw [← 

Depends on / 依赖: AdicCompletion, AdicCompletion.induction_on, AdicCompletion.mk_zero_of, Ideal.exists_pow_inf_eq_pow_smul, LinearMap, LinearMap.ker_eq_bot, Submodule, Submodule.comap_map_eq_of_injective, Submodule.map_smul, Submodule.map_top, comap_map_eq_of_injective, exists_pow_inf_eq_pow_smul, induction_on, inf_le_right, ker_eq_bot, map_smul, map_top, mk_zero_of, nth_rw, smul_mono_right
-/
theorem map_injective {f : M ->ₗ[R] N} (hf : Function.Injective f) :
    Function.Injective (map I f) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a => ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ => ⟨n + k, by lia, n, by lia, ?_⟩⟩
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M)]; rw [Submodule.map_smul'']; rw [Submodule.map_top]
  apply (smul_mono_right _ inf_le_right : I ^ n • (I ^ k • ⊤ ⊓ (range f)) <= _)
  nth_rw 1 [show n = n + k - k by lia]
  rw [← hk (n + k) (show n + k >= k by lia)]
  exact ⟨by simpa using congrArg (fun x => x.val (n + k)) hx, ⟨a (n + k), rfl⟩⟩

end Injectivity

section

variable [IsNoetherianRing R] [Module.Finite R N]

variable {f : M ->ₗ[R] N} {g : N ->ₗ[R] P} (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

section

variable {k : Nat}
  (hkn : forall n >= k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
  (x : AdicCauchySequence I N) (hker : forall (n : Nat), g (x n) in (I ^ n • ⊤ : Submodule R P))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mapExactAuxDelta {n : Nat} {d : N}
  body: have h : f (y - yₙ) in (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) in I ^ (k + n) • ⊤
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exa

中文:
定义 noncomputable
  签名: def mapExactAuxDelta {n : 自然数} {d : N}
  定义体: have h : f (y - yₙ) in (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) in I ^ (k + n) • ⊤
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exa
-/
private noncomputable def mapExactAuxDelta {n : Nat} {d : N}
    (hdmem : d in (I ^ (k + n + 1) • ⊤ : Submodule R N)) {y yₙ : M}
    (hd : f y = x (k + n + 1) - d) (hyₙ : f yₙ - x (k + n) in (I ^ (k + n) • ⊤ : Submodule R N)) :
    { d : (I ^ n • ⊤ : Submodule R M)
      | f (yₙ + d) - x (k + n + 1) in (I ^ (k + n + 1) • ⊤ : Submodule R N) } :=
  have h : f (y - yₙ) in (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) in I ^ (k + n) • ⊤
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exact AdicCauchySequence.mk_eq_mk (by lia) _
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hdmem
  have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ range f) <= I ^ (k + n - k) • (range f) :=
    smul_mono_right _ inf_le_right
  have hyyₙ : y - yₙ in (I ^ n • ⊤ : Submodule R M) := by
    convert_to y - yₙ in (I ^ (k + n - k) • ⊤ : Submodule R M)
    · simp
    · rw [← Submodule.comap_map_eq_of_injective hf (I ^ (k + n - k) • ⊤ : Submodule R M),
        Submodule.map_smul'', Submodule.map_top]
      apply hincl
      rw [← hkn (k + n) (by lia)]
      exact ⟨h, ⟨y - yₙ, rfl⟩⟩
  ⟨⟨y - yₙ, hyyₙ⟩, by simpa [hd, Nat.succ_eq_add_one, Nat.add_assoc]⟩

open Submodule

include hfg in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mapExactAux
  body: (h2 0).choose
    let y := (h2 0).choose_spec.choose
    have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
    have hdmem := (h2 0).choose_spec.choose_spec.left
    ⟨y, by simpa [hdy]⟩
  | .succ n =>
    let d := (h2 <| n + 1).choose
    let y := (h2 <| n + 1).choose_spec.choose

中文:
定义 noncomputable
  签名: def mapExactAux
  定义体: (h2 0).choose
    let y := (h2 0).choose_spec.choose
    have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
    have hdmem := (h2 0).choose_spec.choose_spec.left
    ⟨y, by simpa [hdy]⟩
  | .succ n =>
    let d := (h2 <| n + 1).choose
    let y := (h2 <| n + 1).choose_spec.choose
-/
private noncomputable def mapExactAux :
    (n : Nat) -> { a : M | f a - x (k + n) in (I ^ (k + n) • ⊤ : Submodule R N) }
  | .zero =>
    let d := (h2 0).choose
    let y := (h2 0).choose_spec.choose
    have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
    have hdmem := (h2 0).choose_spec.choose_spec.left
    ⟨y, by simpa [hdy]⟩
  | .succ n =>
    let d := (h2 <| n + 1).choose
    let y := (h2 <| n + 1).choose_spec.choose
    have hdy : f y = x (k + (n + 1)) - d := (h2 <| n + 1).choose_spec.choose_spec.right
    have hdmem := (h2 <| n + 1).choose_spec.choose_spec.left
    let ⟨yₙ, (hyₙ : f yₙ - x (k + n) in (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
      mapExactAux n
    let ⟨d, hd⟩ := mapExactAuxDelta hf hkn x hdmem hdy hyₙ
    ⟨yₙ + d, hd⟩
where
  h1 (n : Nat) : g (x (k + n)) in Submodule.map g (I ^ (k + n) • ⊤ : Submodule R N) := by
    rw [map_smul'']; rw [Submodule.map_top]; rw [range_eq_top.mpr hg]
    exact hker (k + n)
  h2 (n : Nat) : exists (d : N) (y : M),
      d in (I ^ (k + n) • ⊤ : Submodule R N) ∧ f y = x (k + n) - d := by
    obtain ⟨d, hdmem, hd⟩ := h1 n
    obtain ⟨y, hdy⟩ := (hfg (x (k + n) - d)).mp (by simp [hd])
    exact ⟨d, y, hdmem, hdy⟩

end

include hf hfg hg in
/--
theorem `map_exact` / 定理 `map_exact`

English:
theorem map_exact
  statement: Function.Exact (map I f) (map I g)
  proof: by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y => ?_)
  · rw [map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b => ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    

中文:
定理 map_exact
  结论: Function.Exact (map I f) (map I g)
  证明: by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y => ?_)
  · rw [map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b => ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.mk, AdicCompletion, AdicCompletion.induction_on, AdicCompletion.map_zero, AdicCompletion.mk, Ideal.exists_pow_inf_eq_pow_smul, LinearMap, LinearMap.exact_of_comp_eq_zero_of_ker_le_range, LinearMap.range, Submodule, exact_of_comp_eq_zero_of_ker_le_range, exists_pow_inf_eq_pow_smul, hfg.linearMap_comp_eq_zero, induction_on, linearMap_comp_eq_zero, mapExactAux, map_comp, map_zero, x.val
-/
theorem map_exact : Function.Exact (map I f) (map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y => ?_)
  · rw [map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b => ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    have hb (n : Nat) : g (b n) in (I ^ n • ⊤ : Submodule R P) := by
      simpa using congrArg (fun x => x.val n) hz
    let a := mapExactAux hf hfg hg hk b hb
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n => (a n : M)) ?_), ?_⟩
    · refine fun n => SModEq.symm ?_
      simp [a, mapExactAux, SModEq]
    · ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
            Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (show n <= k + n by lia)]
      rw [Submodule.Quotient.eq]
      have hle : (I ^ (k + n) • ⊤ : Submodule R N) <= (I ^ n • ⊤ : Submodule R N) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))
      exact hle (a n).property

end

end AdicCompletion
