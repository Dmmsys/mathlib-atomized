/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!

# The de Rham Period Ring $\mathbb{B}_{dR}^+$ and $\mathbb{B}_{dR}$

In this file, we define the de Rham period ring $\mathbb{B}_{dR}^+$ and
the de Rham ring $\mathbb{B}_{dR}$. We define a generalized version of
these period rings following Scholze. When `R` is the ring of integers
of `ℂₚ` (`PadicComplexInt`), they coincide with the classical de Rham period rings.

## Main definitions

* `BDeRhamPlus` : The period ring $\mathbb{B}_{dR}^+$.
* `BDeRham` : The period ring $\mathbb{B}_{dR}$.

## TODO

1. Extend the θ map to $\mathbb{B}_{dR}^+$
2. Show that $\mathbb{B}_{dR}^+$ is a discrete valuation ring.
3. Show that ker θ is principal when the base ring is integral perfectoid.

Currently, the period ring `BDeRhamPlus` takes the ring of integers `R` as the input.
After the perfectoid theory is developed, we can modify it to
take a perfectoid field as the input.

## Reference

* [Fontaine, *Sur Certains Types de Représentations p-Adiques du Groupe de Galois d'un Corps Local;
  Construction d'un Anneau de Barsotti-Tate*][fontaine1982certains]
* [Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]
* [Scholze, *p-adic Hodge theory for rigid-analytic varieties*][scholze2013adic]

## Tags
Period rings, p-adic Hodge theory
-/

@[expose] public section

universe u

open Ideal WittVector

variable (R : Type u) [CommRing R] (p : Nat) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

local notation "𝕎 " A:100 => WittVector p A
local notation A "♭" => PreTilt A p

noncomputable section

/--
Definition of `fontaineThetaInvertP` / `fontaineThetaInvertP` 的定义

English:
definition fontaineThetaInvertP
  signature: :
  body: Localization.awayLift ((algebraMap R _).comp (fontaineTheta R p)) (p : 𝕎 R♭)
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))

中文:
定义 fontaineThetaInvertP
  签名: :
  定义体: Localization.awayLift ((algebraMap R _).comp (fontaineTheta R p)) (p : 𝕎 R♭)
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))

Depends on / 依赖: IsLocalization, IsLocalization.Away.algebraMap_isUnit, Localization, Localization.awayLift, algebraMap, algebraMap_isUnit, awayLift, fontaineTheta
-/
def fontaineThetaInvertP :
    Localization.Away (p : 𝕎 R♭) ->+* Localization.Away (p : R) :=
  Localization.awayLift ((algebraMap R _).comp (fontaineTheta R p)) (p : 𝕎 R♭)
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))

/--
Definition of `BDeRhamPlus` / `BDeRhamPlus` 的定义

English:
definition BDeRhamPlus
  signature: : Type u
  body: AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away (p : 𝕎 R♭))
deriving CommRing

中文:
定义 BDeRhamPlus
  签名: : 类型u
  定义体: AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away (p : 𝕎 R♭))
deriving CommRing

Depends on / 依赖: AdicCompletion, Localization, Localization.Away, RingHom, RingHom.ker, fontaineThetaInvertP
-/
def BDeRhamPlus : Type u :=
  AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away (p : 𝕎 R♭))
deriving CommRing

/--
Definition of `BDeRham` / `BDeRham` 的定义

English:
definition BDeRham
  signature: : Type u
  body: Localization (M := BDeRhamPlus R p) Submonoid.closure
    AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP R p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP R p)) = Ideal.span {a}}

local notation "𝔹_dR^+(" R ")" => BDeRhamPlus R p
local notation "𝔹_dR(" R ")" => BDeRham R p

中文:
定义 BDeRham
  签名: : 类型u
  定义体: Localization (M := BDeRhamPlus R p) Submonoid.closure
    AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP R p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP R p)) = Ideal.span {a}}

local notation "𝔹_dR^+(" R ")" => BDeRhamPlus R p
local notation "𝔹_dR(" R ")" => BDeRham R p

Depends on / 依赖: AdicCompletion, AdicCompletion.of, BDeRhamPlus, Ideal.span, Localization, RingHom, RingHom.ker, Submonoid, Submonoid.closure, closure, fontaineThetaInvertP
-/
def BDeRham : Type u :=
Localization (M := BDeRhamPlus R p) Submonoid.closure
    AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP R p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP R p)) = Ideal.span {a}}

local notation "𝔹_dR^+(" R ")" => BDeRhamPlus R p
local notation "𝔹_dR(" R ")" => BDeRham R p

end
