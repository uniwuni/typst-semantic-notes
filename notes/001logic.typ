#import "../semantics.typ": *
#import "@preview/theorion:0.3.3": *
#import cosmos.fancy: *
#import "@preview/quick-maths:0.2.1": shorthands
#set text(lang: "en")
#show: show-theorion

= Foundations
== Logic
=== Propositional Logic

#definition(title: "Proposition")[
  A #def(<prop>)[proposition] is a statement that can be assigned a truth value.
]
#names(<prop>, plural: true, "proposition", "statement")

#definition(title: "Tautology")[
  A #def(<tautology>)[tautology] is a #n[proposition] that is always true. Let $dv(P)$ be a #n[proposition], then we denote "$rP$ is a tautology" as $tack.r dv(P)$.
]
#names(<tautology>, plural: true, "tautology", "truth")
#names(<tautology>, "true", "holds", "hold")

#let holds = $#lk(<tautology>, math.tack.r)$
==== Implication
#definition(title: "Implication")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<imp>)[implication] $rP arrow.double rQ$ to be #n[true], one needs a derivation of $holds rQ$ from $holds rP$. 

  In particular, this yields us #def(<imp.modus-ponens>)[modus ponens]: from $holds rP$ and $holds rP arrow.double rQ$, it follows that $holds rQ$.
]
#names(<imp>, "implication", "implications", "implies", "imply", "if", "then")
#names(<imp.modus-ponens>, "modus ponens")


#let imp = $#lk(<imp>, math.arrow.double)$

#remark(title: "Right associativity of implication")[
  For #n[propositions] $dv(P), dv(Q), dv(R)$, we write
  $rP imp rQ imp rR$ for $rP imp (rQ imp rR)$.
]<imp.right-assoc>

#remark(title: "Proving implications")[
  To prove an implication $dv(P) imp dv(Q)$, we usually start our proofs with a sentence along the lines of "Assume $rP$", or, if $rP$ contains a free variable $dv(x)$, "Let $rv(x)$ be $rP$". In the rest of the proof, we are free to use that assumption, as long as we finally show $rQ$.
]

#proposition(title: "Implication basics")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following always #n[hold]: 
  / Reflexivity: $rP imp rP$, <imp.refl>
  / Transitivity: $(rQ imp rR) imp (rP imp rQ) imp rP imp rR$, <imp.trans>
  / Contraction: $(rP imp rP imp rQ) imp rP imp rQ$, <imp.contract>
  / Implication of truths: $rP imp rQ imp rP$, <imp.right-const>
  / Swap: $(rP imp rQ imp rR) imp rQ imp rP imp rR$. <imp.swap>
]
#proof[
  + We need to derive $holds rP$ from $holds rP$. But that is trivial.
  + We need to derive $holds (rP imp rQ) imp rP imp rR$ from 
    $holds rQ imp rR$, e.g. derive $holds rP imp rR$ from 
    $holds rQ imp rR$ and $holds rP imp rQ$,
    so it suffices to derive $holds rR$ from $holds rQ imp rR$, $holds rP imp rQ$, and $holds rP$. 

    From #n[modus ponens], we get $holds rQ$ from $holds rP$, $holds rP imp rQ$. Again using #n[modus ponens] on $holds rQ$ and $holds rQ imp rR$, $holds rR$ follows.
  + Similarly to above, assume $holds rP imp rP imp rQ$ and $holds rP$.
    Then, #n[modus ponens] shows $holds rP imp rQ$, and, again using #n[modus ponens], one has $holds rQ$.
  + Assume $holds rP, holds rQ$. We need to show $holds rP$, but that is 
    already one of our assumptions. $rQ$
  + Assume $holds rP imp rQ imp rR, holds rQ, holds rP$. By #n[modus ponens], $holds rQ imp rR$, by #n[modus ponens], $holds rR$.]

#remark(title: "Omitting the tack")[
  If no confusion arises between asserting the truth of a #n[proposition] $dv(P)$ and just naming it, we often write just $rP$ instead of $holds rP$.
]

==== Conjunction
#definition(title: "Conjunction")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<and>)[conjunction] $rP and rQ$ to be #n[true], both $rP$ and $rQ$ must #n[hold]. Also, from $holds rP and rQ$, one can derive $holds rP$, $holds rQ$.
]
#names(<and>, "logic.and", "logic.as well as", "conjunction", "logic.both", "conjunctions")

#let conj = $#lk(<and>, math.and)$

#proposition(title: "Implication and conjunction")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following always #n[hold]:
  / #n[Conjunction] introduction: $rP imp rQ imp rP conj rQ$, <and.intro>
  / #n[Conjunction] elimination: $rP conj rQ imp rP$, $rP conj rQ imp rQ$, <and.elim>
  / #n[Conjunction] mapping: $(rP imp rQ) imp (rR imp rS) imp (rP conj rR) imp (rQ conj rS)$. <and.map>
]
#proof[
  + Assume $rP, rQ$. Then, by #lk(<and>)[definition], $rP conj rQ$ must hold.
  + Assume $rP conj rQ$. Then we can derive $rP$ and $rQ$ respectively, also by #link(<and>)[definition].
  + Assume $rP imp rQ, rR imp rS, rP conj rR$. Then, by #lk(<and.elim>, [elimination]), we have $rP, rR$. From #n[modus ponens] it follows that $rQ$ as well as $rS$, hence by #lk(<and.intro>,[introduction]), $rQ conj rS$.
  ]
==== Logical equivalence
#definition(title: "Logical equivalence")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, the #n[proposition] given by the #def(<iff>)[equivalence] $rP arrow.l.r.double rQ$ between $rP$, $rQ$ is defined as $(rP imp rQ) conj (rQ imp rP)$. It is often read as "$rP$ iff $rQ$".
]
#names(<iff>, "iff", "if and only if", "equivalently", "biconditional", "biconditionals", "logic.equivalent")
#let iff = $#lk(<iff>, math.arrow.l.r.double)$

#remark(title: "Equivalence conventions")[
  We usually prove #lk(<iff>,[equivalence statements]) by showing both directions. E.g. to prove $dv(P) iff dv(Q)$, we first assume $rP$ and show $rQ$ (the "only if" direction), then assume $rQ$ and show $rP$ (the "if" direction).

  We will also see that if $rP iff rQ$ #n[holds], we can always replace $rP$ by $rQ$ in a #n[statement] without changing whether it is a #n[tautology], which we will often implicitly utilize.

  More fundamentally, if $rP iff rQ$ and $rP$ #n[hold], so must $rQ$, and if $rP iff rQ$ and $rQ$ #n[hold], so must $rP$.
]

#proposition(title: "Logical equivalence is like an equivalence relation")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following must #n[hold]:
  / Reflexivity: $rP iff rP$, <iff.refl>
  / Symmetry: $(rP iff rQ) imp (rQ iff rP)$, <iff.symm>
  / Transitivity: $(rQ iff rR) imp (rP iff rQ) imp (rP iff rR)$, <iff.trans>
]<iff.equiv>
#proof[
  + We must show that $(rP imp rP) and (rP imp rP)$, so it
    suffices#justifyt(<and.intro>) to show $rP imp rP$, $rP imp rP$, 
    both of which are known#justifyt(<imp.refl>).
  + Assume $rP imp rQ, rQ imp rP$. To show $rQ iff rP$, we need   
    to#justifyt(<iff>) deduce $rQ imp rP, rP imp rQ$, which is just our 
    assumptions in reverse order.
  + Assume $rQ imp rR, rR imp rQ, rP imp rQ, rQ imp rP$. We need to show 
    $rP imp rR, rR imp rP$.
    + Assume $rP$. By #n[modus ponens], we have $rQ$, again by
      #n[modus ponens], we have $rR$.
    + Assume $rR$. By #n[modus ponens], we have $rQ$, again by
      #n[modus ponens], we have $rP$.
]

#proposition(title: "Operations respect equivalence")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions] such that $rP iff rQ$ #nn[and][logic] $rR iff rS$. Then, the following must #n[hold]:
  / Equivalence respects equivalence: $(rP iff rR) iff (rQ iff rS)$, <iff.congr>
  / Implication respects equivalence: $(rP imp rR) iff (rQ imp rS)$, <imp.congr>
  / Conjunction respects equivalence: $(rP conj rR) iff (rQ conj rS)$. <and.congr>
]
#proof[
  + One must show $(rP iff rR) imp (rQ iff rS)$, $(rQ iff rS) imp (rP iff rR)$.
    + Assume $rP iff rR$. Then#justifyt(<iff.symm>), $rR iff rP$, such that#justifyt(<iff.trans>) $rR iff rQ$, and#justifyt(<iff.symm>) $rQ iff rR$, such that finally, by #lk(<iff.trans>)[transitivity] and $rR iff rS$, we have $rQ iff rS$.
    + Assume $rQ iff rS$. #lk(<iff.trans>)[Transitivity] with $rP iff rQ$ shows $rP iff rS$. We also have#justifyt(<iff.symm>) $rS iff rR$, such that once again by #lk(<iff.trans>)[transitivity], $rP iff rR$ follows.
  + We show both directions.
    + Assume $rP imp rR$ and $rQ$. From $rP iff rQ$, we can see that $rP$ #n[holds], by #n[modus ponens], so does $rR$, from $rR iff rS$ we can see that $rS$ #n[holds], too. Hence $rQ imp rS$.
    + Assume $rQ imp rS$ and $rP$. From $rP iff rQ$, we can see that $rQ$ #n[holds], by #n[modus ponens], so does $rS$, from $rR iff rS$ we can see that $rR$ #n[holds], too. Hence $rP imp rR$.
  + We show both directions.
    + Assume $rP conj rR$. Then $rP$, $rR$ both #n[hold]#justifyt(<and.elim>). Hence by assumption, so does $rQ$ and $rS$ respectively. Thus#justifyt(<and.intro>) $rQ conj rS$ does too.
    + Assume $rQ conj rS$. Then $rQ$, $rS$ both #n[hold]#justifyt(<and.elim>). Hence by assumption, so does $rP$ and $rR$ respectively. Thus#justifyt(<and.intro>) $rP conj rR$ does too.   
]
#proposition(title: [Properties of conjunction])[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following #n[hold]:
  / Currying: $((rP conj rQ) imp rR)) iff (rP imp rQ imp rR)$. <and.curry>
  / Implying conjunctions: $(rP imp (rQ conj rR)) iff ((rP imp rQ) and (rP imp rR))$, <and.imp-into>
  / Idempotence: $(rP conj rP) iff rP$, <and.self>
  / Commutativity: $(rP conj rQ) iff (rQ conj rP)$, <and.comm>
  / Associativity: $(rP conj (rQ conj rR)) iff ((rP conj rQ) conj rR)$. <and.assoc>
]
#proof[
  + We show both sides.
    + Assume $((rP conj rQ) imp rR), rP, rQ$. Then#justifyt(<and.intro>), we have $rP conj rQ$, hence by #n[modus ponens], $rR$ follows. This shows $rP imp rQ imp rR$.
    + Assume $rP imp rQ imp rR, rP conj rQ$. Then by #lk(<and.elim>)[elimination], $rP$ as well as $rQ$ must be true. Hence by double #n[modus ponens], $rR$ follows. So $(rP conj rQ) imp rR$ must hold.
  + We show both sides.
    + Assume $rP imp (rQ conj rR)$. We need#justifyt(<and.intro>) to show $rP imp rQ$ as well as $rP imp rR$.
      + Assume $rP$. Then by #n[modus ponens], $rQ conj rR$ holds. Thus by #lk(<and.elim>)[elimination], so does $rQ$.
      + Assume $rP$. Then by #n[modus ponens], $rQ conj rR$ holds. Thus by #lk(<and.elim>)[elimination], so does $rR$.
    + Assume $rP imp rQ, rP imp rR, rP$. By #n[modus ponens], we have $rQ, rR$, hence#justifyt(<and.intro>) $rQ conj rR$. This shows $rP imp (rQ conj rR)$.
  + We show both sides. Assume $rP conj rP$, by #lk(<and.elim>)[elimination], $rP$ immediately follows. Now assume $rP$. By #lk(<and.intro>)[introduction], we have $rP imp rP imp rP conj rP$, #lk(<imp.contract>)[contraction] implies $rP imp rP conj rP$ as desired.
  + We show the left-to-right-implication, the other follows from renaming the variables. Assume $rP conj rQ$. Then $rP, rQ$ must hold. Hence $rQ, rP$ hold and by #lk(<and.intro>)[introduction], so does $rQ conj rP$.
  + We show both sides.
    + Assume $rP conj (rQ conj rR)$. By #lk(<and.elim>)[elimination], we have $rP, rQ conj rR$ and finally $rP, rQ, rR$. We use #lk(<and.intro>)[introduction] to show $rP conj rQ$ and use it again to show $(rP conj rQ) conj rR$.
    + Assume $(rP conj rQ) conj rR$. By #lk(<and.elim>)[elimination], we have $rP conj rQ, rR$ and finally $rP, rQ, rR$. We use #lk(<and.intro>)[introduction] to show $rQ conj rR$ and use it again to show $rP conj (rQ conj rR)$.
]
#remark(title: [Associativity of conjunction])[
  By a metamathematical argument, we can see that whatever way we insert brackets in a #n[conjunction] $dv(P)_1 conj dv(P_2) conj dots conj dv(P_n)$, by #lk(<and.assoc>)[associativity], all of them turn out to be equivalent. Hence we omit any discussion of this issue and tacitly assume $conj$ to associate to the, say, left. We will almost never use brackets and instead directly deduce $rP_1, dots, rP_n$ directly from $rP_1 and dots and rP_n$ etc.
]<and.assoc-notation>
==== Disjunction
#let disj = $#lk(<or>, math.or)$
#definition(title: "Conjunction")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<or>)[disjunction] $rP or rQ$ to be #n[true], there are the introduction rules where from $holds rP$ follows $holds rP disj rQ$ and from $holds rQ$ follows $holds rP disj rQ$, as well as the elimination rule where from $holds rP imp rR, holds rQ imp rR$ and $holds rP disj rQ$ one can conclude $rR$.
]
#names(<or>, "or", "disjunction")
#proposition(title: "Implication and disjunction")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following always #n[hold]:
  / #n[Disjunction] introduction: $rP imp rP conj rQ, rQ imp rP conj rQ$, <or.intro>
  / #n[Disjunction] elimination: $(rP imp rR) imp (rQ imp rR) imp (rP disj rQ) imp rR$, <or.elim>
  / #n[Disjunction] mapping: $(rP imp rQ) imp (rR imp rS) imp (rP disj rR) imp (rQ disj rS)$. <or.map>
]
#proof[
  + Follows directly from the introduction rules for #n[disjunction].
  + Follows directly from the elimination rules for #n[disjunction].
  + Assume $rP imp rQ, rR imp rS, rP disj rR$. We show $rP imp rQ disj rS, rR imp rQ disj rS$.
    + Furthermore assume $rP$. Then, by #[modus ponens], $rQ$ holds, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$, as needed.
    + Furthermore assume $rR$. Then, by #[modus ponens], $rS$ holds, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$, as needed.
    Hence we can use #lk(<or.elim>)[elimination] to conclude $(rP disj rR) imp (rQ disj rS)$.
  ]

#proposition(title: [Properties of disjunction])[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following #n[hold]:
  / Disjunction respects equivalence: $rP iff rQ, rR iff rS$ #n[imply] that $(rP disj rR) iff (rQ disj rS)$ <or.congr>
  / Idempotence: $(rP disj rP) iff rP$, <or.self>
  / Commutativity: $(rP disj rQ) iff (rQ disj rP)$, <or.comm>
  / Associativity: $(rP disj (rQ disj rR)) iff ((rP disj rQ) disj rR)$,<or.assoc>
  / Conjunction Distributivity: $rP disj (rQ conj rR) iff ((rP disj rQ) conj (rP disj rR))$ <or.and-assoc> and $rP conj (rQ disj rR) iff ((rP conj rQ) disj (rP conj rR))$, <and.or-assoc>
  / Absorption Laws: $(rP disj (rP conj rQ)) iff rP$ <or.and-absorb>, $(rP conj (rP disj rQ)) iff rP$, <and.or-absorb>
  / Disjunction, implication and conjunction: $((rP disj rQ) imp rR) iff ((rP imp rR) and (rQ imp rR))$.
  ]
#proof[
  + We show both directions.
    + Apply #lk(<or.elim>)[elimination] to $rP disj rR$.
      + Assume $rP$ holds, then by assumption, so does $rQ$, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$.
      + Assume $rR$ holds, then by assumption, so does $rS$, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$.
    + Identical argument up to renaming and symmetry.
  + $(rP disj rP) imp rP$ follows from #lk(<or.elim>)[elimination] and #lk(<imp.refl>)[reflexivity of implication], $rP imp rP disj rP$ is just #lk(<or.intro>)[introduction].
  + Assume $rP disj rQ$. Applying #lk(<or.elim>)[elimination], we need to show that $rP imp rQ disj rP$, $rQ imp rQ disj rP$, both of which are instances of #lk(<or.intro>)[introduction]. The other direction is the same up to renaming.
  + We show the left-to-right-case, the other one follows similarly.
    Assume $rP disj (rQ disj rR)$ and apply #lk(<or.elim>)[elimination].
    + We need to show $(rP disj rQ) disj rR$ from $rP$. But this is just two instances of #lk(<or.intro>)[introduction].
    + We need to show $(rP disj rQ) disj rR$ from $rQ disj rR$. Applying #lk(<or.elim>)[elimination] to $rQ disj rR$, it remains to be shown that $rQ imp ((rP disj rQ) disj rR)$ and $rR imp ((rP disj rQ) disj rR)$.
      + Follows from two instances of #lk(<or.intro>)[introduction].
      + Follows from one instance of #lk(<or.intro>)[introduction].
  + We show both laws and both directions.
    + Assume $rP disj (rQ conj rR)$. Apply #lk(<or.elim>)[elimination].
      + Assume $rP$. Then, $rP disj rQ$, $rP disj rR$ hold by left #lk(<or.intro>)[introduction], and so does $(rP disj rQ) conj (rP disj rR)$, by #lk(<and.intro>)[conjunction introduction].
      + Assume $rQ conj rR$. Then, $rP disj rQ$, $rP disj rR$ hold by two right #lk(<or.intro>)[introductions], and so does $(rP disj rQ) conj (rP disj rR)$, by #lk(<and.intro>)[conjunction introduction].
    + Assume $(rP disj rQ) conj (rP disj rR)$, hence we can assume $rP disj rQ$, $rP disj rR$. Apply #lk(<or.elim>)[elimination] on the first.
      + Assume $rP$: Then by #lk(<or.intro>)[introduction], $rP disj (rQ conj rR)$ holds.
      + Assume $rQ$: Do the same on $rP disj rR$ - if $rP$ holds, use #lk(<or.intro>)[introduction] directly, if $rR$ holds, then so does $rQ conj rR$ by #lk(<and.intro>)[introduction], hence by #lk(<or.intro>)[disjunction introduction], we get $rP disj (rQ conj rR)$.
    + Assume $rP conj (rQ disj rR)$, such that we have $rP$ and $rQ disj rR$. Apply #lk(<or.elim>)[elimination] on the #n[disjunction].
      + If we have $rQ$, then $rP conj rQ$ holds, hence $(rP conj rQ) disj (rP conj rR)$ does.
      + If we have $rR$, then $rP conj rR$ holds, hence $(rP conj rQ) disj (rP conj rR)$ does.
    + Assume $(rP conj rQ) disj (rP conj rR)$ holds and use #lk(<or.elim>)[elimination].
      + If $rP conj rQ$ is true, so are $rP, rQ$. Hence $rQ disj rR$ is, and finally $rP conj (rQ disj rR)$.
      + If $rP conj rQ$ is true, so are $rP, rR$. Hence $rQ disj rR$ is, and finally $rP conj (rQ disj rR)$.
  + We show both directions of both laws.
    + Assume $rP disj (rP conj rQ)$ and use #lk(<or.elim>)[elimination].
      If $rP$ is true, we are done, if $rP conj rQ$ is, $rP$ also follows#justifyt(<and.elim>).
    + Assume $rP$, then $rP disj (rP conj rQ)$ immediately#justifyt(<or.intro>) follows.
    + Assume $rP conj (rP disj rQ)$. Then $rP$ follows by #lk(<and.elim>)[elimination].
    + Assume $rP$, then $rP disj rQ$ is true#justifyt(<or.intro>), and so must their #n[conjunction] be#justifyt(<and.intro>), as needed.
  + We show both directions.
    + Assume $(rP disj rQ) imp rR$, we need to show $rP imp rR, rQ imp rR$.
      + Assume $rP$, then $rP disj rQ$ holds, hence by #n[modus ponens], we have $rR$, such that $rP imp rR$.
      + Assume $rQ$, then we have $rP disj rQ$ and proceed similarly.
    + Assume $(rP imp rR) conj (rQ imp rR)$, e.g. $rP imp rR, rQ imp rR$, and $rP disj rQ$. Use #lk(<or.elim>)[elimination] and $rR$ immediately follows.      
]
==== Falsehood and negation
Until now we have only covered a fairly small fragment of propositional logic, e.g. a positive one. By introducing negation, we add substantial complexity and raise some more foundational questions.

#definition(title: "Falsehood")[
  The #def(<false>)[false] #n[proposition] $bot$ is defined such that if $bot$ #n[holds], so does any #n[proposition] $dv(P)$.
]
#names(<false>, "false", "absurd", "contradiction", "contradictions", "falsehood", "absurdity")
#let fls = $#lk(<false>, math.bot)$
#definition(title: "Negation")[
  For any #n[proposition] $dv(P)$, define its #def(<not>)[negation] $not rP$ as $rP imp fls$.
]

#names(<not>, "not", "negation")
#let neg = $#lk(<not>, math.not)$

#definition(title: "Truth")[
  Define the #def(<true>)[true] #n[proposition] $top$ as $neg fls$.
]
#names(<true>, "truth", "triviality")
#let tru = $#lk(<true>, math.top)$

#proposition(title: "True and false")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, the following #n[hold]:
  / Elimination of #n[falsehood]: $fls imp rP$, <false.elim>
  / #n[Falsehood] is false: $neg fls$, <false.false>
  / #n[Truth] is true: $tru$, <true.true>
  / Truth values and #n[biconditionals]: $(tru iff rP) iff rP$, <iff.true> $(fls iff rP) iff neg rP$, <iff.false>
  / Truth values and #n[implications]: $(tru imp rP) iff rP$, $(fls imp rP) iff tru$, $(rP imp tru) iff tru$, $(rP imp fls) iff neg rP$, <imp.true-false>
  / Truth values and #n[conjunction]: $(tru conj rP) iff rP$, $(fls conj rP) iff fls$, <conj.true-false>
  / Truth values and #n[disjunction]: $(tru disj rP) iff tru$, $(fls disj rP) iff rP$, <disj.true-false>
  / Truth values and #n[negation]: $neg tru iff fls, neg fls iff tru$, <not.true-false>
  / Absurdity: $neg (rP conj neg rP)$, <conj.absurd>  
  / Converse implications: $(rP imp rQ) imp neg rQ imp neg rP$, <imp.converse1>
  / #n[Negation] respects equivalence: $(rP iff rQ) imp (neg rP iff neg rQ)$ <not.congr>
]
#proof[
  + By definition of $fls$.
  + $neg fls iff (fls imp fls)$, which holds by #lk(<imp.refl>)[reflexivity].
  + Follows from $tru iff neg fls$.
  + If $tru iff rP$, then, since $tru$ is#justifyt(<true.true>) #n[true], so is $rP$. If $rP$ holds, then it also follows from $tru$ such that $rP imp tru$ and the other direction holds anyways.

    If $fls iff rP$, then in particular $(rP imp fls) iff neg P$. If $neg P$ holds, we have $rP imp fls$, and $fls imp rP$ holds anyways#justifyt(<false.elim>), so the #n[biconditional] is established.
  + We show all #n[biconditionals].
    + We have $rP #justify(<iff.true>, iff) (tru iff rP) #justify(<iff>, iff) ((tru imp rP) conj (rP imp tru))$, but the second #n[proposition] is #n[true],#justifyt(<imp.right-const>) as $tru$ is#justifyt(<true.true>), such that the #n[conjunction] is #nn[equivalent][logic] to $tru imp rP$ as desired.
    + By the #lk(<iff.true>)[above]#justifyt(<iff.trans>), we need to show $fls imp rP$ always holds. But that is already #lk(<false.elim>)[known].
    + It suffices#justifyt(<iff.true>) to show $rP imp tru$. But that follows#justifyt(<imp.right-const>) from the #lk(<true.true>)[fact] that $tru$ is #n[true].
    + By #lk(<not>)[definition] and #lk(<imp.refl>)[reflexivity] of #n[implication].
  + We show both #n[biconditionals].
    + $tru conj rP imp rP$ is clear. Assume $rP$, then $tru$ #lk(<true.true>)[is] also #n[true], hence so is $tru conj rP$.
    + $bot conj rP imp bot$ is clear, the other direction follows from #lk(<false.elim>)[falsehood elimination].
  + We show both #n[biconditionals].
    + $tru imp (tru disj rP)$ follows from #lk(<or.intro>)[introduction], the other direction from the #lk(<true.true>)[fact] that $tru$ is #n[true].
    + $P imp (fls disj rP)$  follows from #lk(<or.intro>)[introduction], the other direction from #lk(<or.elim>)[elimination] as well as the #lk(<false.elim>)[fact] that $fls imp rP$ and $rP imp rP$#justifyt(<imp.refl>)
  + We show both #n[biconditionals].
    + We have $not tru #justify(<true>,iff) not not fls iff ((fls imp fls) imp fls)$. But $fls imp fls$ holds#justifyt(<imp.refl>), hence by #n[modus ponens] we have $neg tru imp bot$. The other direction is obvious from #lk(<false.elim>)[elimination].
    + By #lk(<true>)[definition].
  + Assume $rP and neg rP$. Then we have $rP, neg rP$, but $neg rP #justify(<not>,iff) (rP imp fls)$, hence by #n[modus ponens], $fls$ holds.
  + Rewrite $neg rP$ to#justifyt(<not>) $rP imp fls$, $neg rQ$ to $rQ imp fls$. Then, this follows from #lk(<imp.trans>)[transitivity of implications].
  + Assume $rP iff rQ$. To show $neg rP imp neg rQ$, apply #lk(<imp.converse1>)[the previous statement] to $rP imp rQ$, and similarly for the other direction.
]
