#import "001logic.typ": *
== Basic set theory
This part is largely oriented around the first few chapters of @axiomatic-set-theory due to its detailed and rigorous treatment of the very basics of set theory as a foundation.

Over the last few sections, we have developed the first steps of a theory of #n[terms], but without any interpretation attached, leaving it unclear what they should represent. This is mostly an advantage that leaves the developed first-order logic very general and makes it able to contain topics as distinct as abelian groups and dense linear orders. 

However, from now on we will consider #n[terms] as standing for _sets_ --- what these are remains undefined, but every single concept we concern ourselves with can be reduced to a construct of sets. Of course, there are other foundations, some of which, like many type theories, more closely match the informal foundations used in everyday mathematics.
But they are substantially harder to develop formally and there is still too much disagreement about which of the dozens of slightly different theories should be preferred, disagreement that has mostly been settled for set theory (unless, of course, you start talking to set theorists).

Hence from now on, the following "definition" applies:
#definition(title: "Sets")[
  A #def(<set>)[set] is anything quantified over, i.e. the preferred interpretation of the elements of the universe the variables range over.
]
#names(<set>,"set","sets")
#n[Sets] are defined by their elements, hence we need a notion of elements. In informal mathematics one usually considers #n[sets] of numbers, group elements, fruit (mostly occurring on primary school level) and so forth.
While we will be able to deal with most of these by defining them into #n[existence] (excluding the fruit), currently the only thing a #n[set] can contain is other #n[sets]. Hence we declare:
#definition(title: "Membership")[
  If $dv(t), dv(s)$ are two #n[terms], then $rt in rs$ (read: $rt$ is an element of $rs$) is a #n[proposition] that expresses #def(<mem>)[membership] of $rt$ in $rs$.
]
#let mem = $#lk(<mem>, math.in)$
#let nmem = $#lk(<mem>, math.in.not)$
#names(<mem>, "element","member",plural:true)
#names(<mem>, "in")

Admittedly this is less of a definition than it is a declaration or an axiom, since $dv(t) mem dv(s)$ is not assigned any definiens.

We take an _extensional_ point of view in which #n[sets] are fully defined by their #n[elements] as opposed to some other structure that only changes how we arrive at their elements. These _intensional_ equalities often make sense in more computational theories as they can incorporate algorithmic complexity or termination behavior.

#axiom(title: "Extensionality")[
  #n[For all] #n[sets] $dv(x),dv(y)$,
  $ (forall(z) rz mem rx iff rz mem ry) imp rx=ry. $
]<set.ext>
#names(<set.ext>, "extensionality")

We will often end up with collections that are too large to be a #n[set], e.g. the collection of all groups. This requires us to deal with _classes_.

#definition(title: "Class")[
  A #def(<class>)[class] is a definable property of #n[sets], e.g. a #n[proposition] $dv(P)(dv(x), dv(a_1), ..., dv(a_n))$. We write $dv(x) in rP$ #n[iff] $rP(rx)$. Two classes $dv(P), dv(Q)$ are considered equal if $forall(x)rP(rx) iff rQ(rx)$. To emphasize that a #n[proposition] is viewed as a class, we write ${dv(x) mid(|) rP(rx, rv(a_1), dots, rv(a_n))}$. We will use usual $defeq$-notation for classes, too.
]
#let classcompr(x,P) = ${dv(#x) #link(<class>,$mid(|)$) #P}$
#names(<class>,"class","classes")
Lots of constructions that go through with #n[sets] also work with #n[classes], as long as they do not require collecting subsets. We will expect the reader to handle this implicitly unless noted otherwise, since the cases where this is used are relatively simple.
#remark(title: [Sets as classes])[
  #n[Sets] can be viewed as certain #n[classes]: If $dv(x)$ is a #n[set], $classcompr(y, ry mem rx)$ is a #n[class] such that #n[for all] $dv(y)$, $ry mem rx iff ry mem classcompr(y, ry mem rx)$. We will use this conversion implicitly when needed. Clearly, if a #n[class] arises from two #n[sets], they must be #n[equal] by the axiom of #n[extensionality]. Hence a #n[class] that is proven arise from a #n[set] suffices to define that #n[set].
]<set.to-class>

#definition(title: "Proper class")[
  A #def(<class.proper>)[proper class] is a #n[class] $dv(A)$ that does not arise from a #n[set] in the #lk(<set.to-class>)[above way], i.e. there does not #n[exist] any #n[set] $dv(x)$ such that #n[for all] #n[sets] $dv(y)$, $ry mem rx iff ry mem rA$.
]

#names(<class.proper>, "proper class", "proper classes")
#example(title: "Russell's paradox")[
  It is not immediately clear that there are any #n[proper classes]. But let us define $dv(R) defeq classcompr(x, dv(x) nmem dv(x))$. If $rR$ were not #lk(<class.proper>)[proper], there would be a #n[set] $dv(r)$ with $dv(x) mem rr iff rx nmem rx$. Hence $das(1,rr mem rr iff rr nmem rr)$. With #n[excluded middle], it is very easy to derive a #n[contradiction], but let us work around it:

  We have $das(3,rr nmem rr)$: If $das(2,rr mem rr)$, $rr nmem rr$ follows#justifytas(1), hence $fls$.
  Now again by assumption#justifytas(1,3), this also means we have $das(4,rr mem rr)$, #n[contradiction] #justifytas(3,4).

  So such a #n[set] cannot #n[exist] even intutitionistically.
]
=== Constructing basic sets
==== Pairing
#axiom(title: "Axiom of pairing")[
  For #n[all] #n[sets] $dv(x),dv(y)$, the #n[class] $classcompr(a, a = x disj a = y)$ is a #n[set].
]<set.ax-pairing>
#let upair(x,y) = $#link(<unordered-pair>,${$)#x,#y#link(<unordered-pair>,$}$)$
#let singleton(x) = $#link(<set.singleton>,${$)#x#link(<set.singleton>,$}$)$
#definition(title: "Unordered pair")[
  For #n[all] #n[sets] $dv(x),dv(y)$, define the #n[set] we call their #def(<unordered-pair>)[unordered pair] as $ {rx,ry} defeq classcompr(a, ra = rx disj ra = ry). $ Also define the #def(<set.singleton>)[singleton #n[set]] ${rx}$ containining $rx$ as $upair(rx,rx)$.
]
#names(<unordered-pair>, "unordered pair")
#names(<set.singleton>, "singleton")
#proof(title: "Proof of well-definedness")[
  #n[For any] #n[sets] $dv(x), dv(y)$, $upair(x,y)$ is a #n[set] due to the #lk(<set.ax-pairing>)[axiom of pairing]. It is unique since it is defined by a #n[class]#justifyt(<set.to-class>). This also implies the well-definedness of $singleton(x)$. 
]
#proposition(title: "Pairs and singletons")[
  Let $dv(a), dv(w), dv(x),dv(y), dv(z)$ be #n[sets]. Then, the following hold:
  + $ra mem upair(rx,ry) iff ra = rx disj ra = ry$, <unordered-pair.mem-iff>
  + $ra mem singleton(rx) iff ra = rx$, <set.singleton.mem-iff>
  + $singleton(rx) = singleton(ry) iff rx = ry$, <set.singleton-eq-singleton>
  + $rx = ry iff forall(v) rx mem rv(v) iff ry mem rv(v)$, <set.eq-iff-mem-same>
  + $upair(rw,rx) = upair(ry,rz) iff (rw = ry conj rx = rz) disj (rw = rz conj rx = ry)$, <unordered-pair.eq-unordered-pair>
  + $upair(rx,ry) = upair(ry,rx)$. <unordered-pair.comm>
]
#proof[
  + By #lk(<unordered-pair>)[definition].
  + Compare
    $ra mem singleton(rx) #justify(<set.singleton>, iff) ra mem upair(rx, rx) #justify(<set.singleton>, iff) ra = rx disj ra = rx #justify(<or.self>, iff) a = x.$
  + The right-to-left-direction is obvious from #lk(<eq.subst>)[substitution]. Now let $singleton(rx) = singleton(ry)$. Then by #lk(<eq.subst>)[substitution] $rx mem singleton(rx) iff rx mem singleton(ry)$. From #lk(<set.singleton.mem-iff>)[the previous], this can be rewritten to $rx = rx iff rx = ry$, hence#justifyt(<eq.refl>) $rx = ry$.
  + Left-to-right is clear. Now assume $forall(v) rx mem rv(v) iff ry mem rv(v)$. Choose $dv(v) := singleton(ry)$. Hence 
    $rx mem singleton(ry) iff ry mem singleton(ry)$, so #lk(<set.singleton.mem-iff>)[from the previous], $rx = ry iff ry = ry$ and $rx = ry$ follows#justifyt(<eq.refl>).
  + We show both directions.
    + Assume $upair(rw,rx) = upair(ry,rz)$.
      Then#justifyt(<unordered-pair.mem-iff>) we have $rw mem upair(ry,rz) iff rw = ry disj rw = rz$ and similarly
      $rx = ry disj rx = rz$. We need to exclude the two cases
      $rw = ry conj rx = ry, rw = rz conj rx = rz$.

      If $rw = ry = rx$, from $upair(rw,rx) = upair(ry,rz)$ we know that $rz mem upair(rw,rx)$ hence $rz = rw disj rz = rx = rw$. Thus $rw = rx = ry = rz$ and the #n[disjunction] also holds. Similar reasoning for the case $rw = rz = rx$.
    + First, assume $rw = ry, rx = rz$. Then for any #n[set] $dv(a)$,
      $ ra in upair(rw,rx) #justify(<unordered-pair.mem-iff>,iff) ra = rw disj ra = rx #justify(<eq.trans>,iff) ra = ry disj ra = rz #justify(<unordered-pair.mem-iff>,iff) ra in upair(ry,rz). $
      Now, assume $rw = rz, rx = ry$. Then for any #n[set] $dv(a)$,
      $ ra in upair(rw,rx) #justify(<unordered-pair.mem-iff>,iff) ra = rw disj ra = rx #justify(<eq.trans>,iff) ra = rz disj ra = ry #justify(<or.comm>,iff) ra = ry disj ra = rz#justify(<unordered-pair.mem-iff>,iff) ra in upair(ry,rz). $
      In both cases, use #n[extensionality] to conclude $upair(rw,rx) = upair(ry,rz)$.
  + Apply the #lk(<unordered-pair.eq-unordered-pair>)[previous proposition]. Then it suffices to show that $rx = ry conj rx = ry$, which is clear.
  ]
#let pair(x,y) = $#link(<pair>,$($)#x,#y#link(<pair>,$)$)$
#let tuple(..args) = $#link(<tuple>,$($) #args.pos().join([, ])#link(<tuple>,$)$)$
#definition(title: "Ordered pairs and tuples")[
  Let $dv(x),dv(y)$ be #n[sets]. Then, we define the #def(<pair>)[ordered pair] (or just _pair_) of $rx, ry$ as 
  $ (rx,ry) defeq upair(singleton(rx), upair(rx,ry)). $
  If we are given #n[sets] $dv(x)_dv(i)$ for $1 <= ri <= dv(n)$, then
  we metamathematically define #def(<tuple>)[tuples]
  $ (dv(x)_1, dots, rx_(rn-1), rx_rn) defeq pair((rx_1, dots, rx_(rn-1)), rx_rn) $ 
  for all numbers $rn >= 3$.
]
#names(<pair>, plural:true, "pair", "ordered pair")
#names(<tuple>, plural:true, "tuple", "ordered tuple", "triple", "ordered triple")
#lemma(title: [Equality of ordered pairs])[
  #n[For all] #n[sets] $dv(w),dv(x),dv(y),dv(z)$ we have 
  $ pair(rw,rx) = pair(ry,rz) iff rw = ry conj rx = rz. $ <pair.eq-pair>
  Immediately, this #n[implies] that for #n[sets] $dv(x)_dv(i), dv(y)_dv(j)$ for $1 <= ri, rj <= dv(n)$, we have 
  $  tuple(rx_1, dots, rx_n) = tuple(ry_1, dots, ry_n) iff rx_1 = ry_1 conj dots conj rx_n = ry_n. $ <tuple.eq-tuple>
]
#proof[
  The right-to-left #n[implication] is clear.
  So assume
  $ pair(rw,rx) = upair(singleton(rw), upair(rw,rx)) = upair(singleton(ry), upair(ry,rz)) = pair(ry,rz). $
  Then, as #lk(<unordered-pair.eq-unordered-pair>)[shown above], there are two cases to cover:
  + $singleton(rw) = singleton(ry) #justify(<set.singleton-eq-singleton>,iff) rw = ry, upair(rw,rx) = upair(ry,rz)$: Then, as #lk(<unordered-pair.eq-unordered-pair>)[shown above], either $rw = ry, rx = rz$ or $rw = rz, rx = ry$. The first case amounts to precisely what we want to show, the second case implies $rw=rx=ry=rz$ hence $rw = ry, rx = rz$.
  + $singleton(rw) = upair(ry,rz), upair(rw,rx) = singleton(ry)$:
    Then#justifyt(<set.singleton.mem-iff>) $ry = rw, rz = rw, rw = ry, rx = ry$ such that $rw = ry$, $rx = rz$ as required.
]
#remark[
  This is the first instance of a common phenomenon in mathematics where a concrete construction of an object is irrelevant to its usage and what matters instead are properties that define its behavior more or less uniquely.

  For example it does not matter that a #n[ordered pair] of $dv(x),dv(y)$ is defined as $upair(singleton(rx), upair(rx,ry))$ and indeed, we will almost never see that #n[term] again. What we care about instead is that we _can_ always construct an #n[ordered pair] and that it is already determined by its two components.
]

==== Union  
#axiom(title: [Axiom of unions])[
  For #n[every] #n[set] $dv(x)$, the #n[class] $classcompr(a, exists(y) ry mem rx conj ra mem ry)$ is a #n[set].
]<set.ax-union>
#let setUnion(a) = link(<set.Union>)[$union.big #a$]
#definition(title: "Union of a set")[
  For #n[every] #n[set] $dv(x)$, define the #n[set] we call its #def(<set.Union>)[union] as $ setUnion(rx) defeq classcompr(a, exists(y) ry mem rx conj ra mem ry). $
]
#names(<set.Union>, "union of a set", "union.set")
#proof(title: "Proof of well-definedness")[Well-defined due to the #lk(<set.ax-union>)[axiom of unions].]
#let union = link(<set.union>)[$union$]
#definition(title: "Union of two sets")[
  For #n[all] #n[sets] $dv(x), dv(y)$, define the #n[set] we call their #def(<set.union>)[union] (or _binary union_) as $ rx union ry defeq setUnion(upair(rx,ry)). $
]
#names(<set.union>, "binary union", "union")