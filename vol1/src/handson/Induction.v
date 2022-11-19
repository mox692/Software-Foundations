(** * Basics: Functional Programming in Coq *)

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
*)

(* ################################################################# *)
(** * Introduction *)

(** The functional style of programming is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions as _first-class_ values --
    i.e., values that can be passed as arguments to other functions,
    returned as results, included in data structures, etc.  The
    recognition that functions can be treated as data gives rise to a
    host of useful and powerful programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and _polymorphic
    type systems_ supporting abstraction and code reuse.  Coq offers
    all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's native functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Gallina programs. *)

(* ################################################################# *)
(** * Data and Functions *)

(* ================================================================= *)
(** ** Enumerated Types *)

(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions.  To
    illustrate this, in this course we will explicitly recapitulate
    (almost) all the definitions we need, rather than getting them
    from the standard library. *)

(* ================================================================= *)
(** ** Days of the Week *)

(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a set of data values -- a _type_. *)

    Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.
  
  (** The new type is called [day], and its members are [monday],
      [tuesday], etc.
  
      Having defined [day], we can write functions that operate on
      days. *)
  
  (** here is memos **)
  Definition next_weekday (d:day) : day :=
    match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
    end. 
  
  (** One point to note is that the argument and return types of
      this function are explicitly declared.  Like most functional
      programming languages, Coq can often figure out these types for
      itself when they are not given explicitly -- i.e., it can do _type
      inference_ -- but we'll generally include them to make reading
      easier. *)
  
  (** Having defined a function, we should next check that it
      works on some examples.  There are actually three different ways
      to do the examples in Coq.  First, we can use the command
      [Compute] to evaluate a compound expression involving
      [next_weekday]. *)
  
  Compute (next_weekday friday).
  (* ==> monday : day *)
  
  Compute (next_weekday (next_weekday saturday)).
  (* ==> tuesday : day *)
  
  (** (We show Coq's responses in comments, but, if you have a
      computer handy, this would be an excellent moment to fire up the
      Coq interpreter under your favorite IDE -- either CoqIde or Proof
      General -- and try it for yourself.  Load this file, [Basics.v],
      from the book's Coq sources, find the above example, submit it to
      Coq, and observe the result.) *)
  
  (** Second, we can record what we _expect_ the result to be in the
      form of a Coq example: *)
  
  Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.
  
  (** This declaration does two things: it makes an
      assertion (that the second weekday after [saturday] is [tuesday]),
      and it gives the assertion a name that can be used to refer to it
      later.  Having made the assertion, we can also ask Coq to verify
      it like this: *)
  
  Proof. simpl. reflexivity.  Qed.
  
  (** The details are not important just now, but essentially this
      can be read as "The assertion we've just made can be proved by
      observing that both sides of the equality evaluate to the same
      thing."
  
      Third, we can ask Coq to _extract_, from our [Definition], a
      program in another, more conventional, programming
      language (OCaml, Scheme, or Haskell) with a high-performance
      compiler.  This facility is very interesting, since it gives us a
      path from proved-correct algorithms written in Gallina to
      efficient machine code.  (Of course, we are trusting the
      correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
      extraction facility itself, but this is still a big step forward
      from the way most software is developed today.) Indeed, this is
      one of the main uses for which Coq was developed.  We'll come back
      to this topic in later chapters. *)
  
  (* ================================================================= *)
  (** ** Homework Submission Guidelines *)
  
  (** If you are using _Software Foundations_ in a course, your
      instructor may use automatic scripts to help grade your homework
      assignments.  In order for these scripts to work correctly (and
      give you that you get full credit for your work!), please be
      careful to follow these rules:
        - Do not change the names of exercises. Otherwise the grading
          scripts will be unable to find your solution.
        - Do not delete exercises.  If you skip an exercise (e.g.,
          because it is marked "optional," or because you can't solve it),
          it is OK to leave a partial proof in your [.v] file; in
          this case, please make sure it ends with [Admitted] (not, for
          example [Abort]).
        - It is fine to use additional definitions (of helper functions,
          useful lemmas, etc.) in your solutions.  You can put these
          before the theorem you are asked to prove.
        - If you introduce a helper lemma that you end up being unable
          to prove, hence end it with [Admitted], then make sure to also
          end the main theorem in which you use it with [Admitted], not
          [Qed].  That will help you get partial credit, in case you
          use that main theorem to solve a later exercise.
  
      You will also notice that each chapter (like [Basics.v]) is
      accompanied by a _test script_ ([BasicsTest.v]) that automatically
      calculates points for the finished homework problems in the
      chapter.  These scripts are mostly for the auto-grading
      tools, but you may also want to use them to double-check
      that your file is well formatted before handing it in.  In a
      terminal window, either type "[make BasicsTest.vo]" or do the
      following:
  
         coqc -Q . LF Basics.v
         coqc -Q . LF BasicsTest.v
  
      See the end of this chapter for more information about how to interpret
      the output of test scripts.
  
      There is no need to hand in [BasicsTest.v] itself (or [Preface.v]).
  
      If your class is using the Canvas system to hand in assignments...
        - If you submit multiple versions of the assignment, you may
          notice that they are given different names.  This is fine: The
          most recent submission is the one that will be graded.
        - To hand in multiple files at the same time (if more than one
          chapter is assigned in the same week), you need to make a
          single submission with all the files at once using the button
          "Add another file" just above the comment box. *)
  
  (** The [Require Export] statement on the next line tells Coq to use
      the [String] module from the standard library.  We'll use strings
      ourselves in later chapters, but we need to [Require] it here so
      that the grading scripts can use it for internal purposes. *)
  From Coq Require Export String.
  
  (* ================================================================= *)
  (** ** Booleans *)
  
  (** Following the pattern of the days of the week above, we can
      define the standard type [bool] of booleans, with members [true]
      and [false]. *)
  
  Inductive bool : Type :=
    | true
    | false.
  
  (** Functions over booleans can be defined in the same way as
      above: *)
  
  Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.
  
  Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.
  
  Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.
  
  (** (Although we are rolling our own booleans here for the sake
      of building up everything from scratch, Coq does, of course,
      provide a default implementation of the booleans, together with a
      multitude of useful functions and lemmas.  Whenever possible,
      we'll name our own definitions and theorems so that they exactly
      coincide with the ones in the standard library.) *)
  
  (** The last two of these illustrate Coq's syntax for
      multi-argument function definitions.  The corresponding
      multi-argument application syntax is illustrated by the following
      "unit tests," which constitute a complete specification -- a truth
      table -- for the [orb] function: *)
  
  Example test_orb1:  (orb true  false) = true.  
  Proof. simpl. reflexivity.  Qed.
  Example test_orb2:  (orb false false) = false.
  Proof. simpl. reflexivity.  Qed.
  Example test_orb3:  (orb false true)  = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_orb4:  (orb true  true)  = true.
  Proof. simpl. reflexivity.  Qed.
  
  (** We can also introduce some familiar infix syntax for the
      boolean operations we have just defined. The [Notation] command
      defines a new symbolic notation for an existing definition. *)
  
  Notation "x && y" := (andb x y).
  Notation "x || y" := (orb x y).
  
  Example test_orb5:  false || false || true = true.
  Proof. simpl. reflexivity. Qed.
  
  (** _A note on notation_: In [.v] files, we use square brackets
      to delimit fragments of Coq code within comments; this convention,
      also used by the [coqdoc] documentation tool, keeps them visually
      separate from the surrounding text.  In the HTML version of the
      files, these pieces of text appear in a [different font]. *)
  
  (** These examples are also an opportunity to introduce one more small
      feature of Coq's programming language: conditional expressions... *)
  
  Definition negb' (b:bool) : bool :=
    if b then false
    else true.
  
  Definition andb' (b1:bool) (b2:bool) : bool :=
    if b1 then b2
    else false.
  
  Definition orb' (b1:bool) (b2:bool) : bool :=
    if b1 then true
    else b2.
  
  (** Coq's conditionals are exactly like those found in any other
      language, with one small generalization.  Since the [bool] type is
      not built in, Coq actually supports conditional expressions over
      _any_ inductively defined type with exactly two clauses in its
      definition.  The guard is considered true if it evaluates to the
      "constructor" of the first clause of the [Inductive]
      definition (which just happens to be called [true] in this case)
      and false if it evaluates to the second. *)
  
  (** **** Exercise: 1 star, standard (nandb)
  
      The command [Admitted] can be used as a placeholder for an
      incomplete proof.  We use it in exercises to indicate the parts
      that we're leaving for you -- i.e., your job is to replace
      [Admitted]s with real proofs.
  
      Remove "[Admitted.]" and complete the definition of the following
      function; then make sure that the [Example] assertions below can
      each be verified by Coq.  (I.e., fill in each proof, following the
      model of the [orb] tests above, and make sure Coq accepts it.) The
      function should return [true] if either or both of its inputs are
      [false].
  
      Hint: if [simpl] will not simplify the goal in your proof, it's
      probably because you defined [nandb] without using a [match]
      expression. Try a different definition of [nandb], or just
      skip over [simpl] and go directly to [reflexivity]. We'll
      explain this phenomenon later in the chapter. *)
  
  Definition nandb (b1:bool) (b2:bool) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_nandb1:               (nandb true false) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb2:               (nandb false false) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb3:               (nandb false true) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb4:               (nandb true true) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** **** Exercise: 1 star, standard (andb3)
  
      Do the same for the [andb3] function below. This function should
      return [true] when all of its inputs are [true], and [false]
      otherwise. *)
  
  Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_andb31:                 (andb3 true true true) = true.
  (* FILL IN HERE *) Admitted.
  Example test_andb32:                 (andb3 false true true) = false.
  (* FILL IN HERE *) Admitted.
  Example test_andb33:                 (andb3 true false true) = false.
  (* FILL IN HERE *) Admitted.
  Example test_andb34:                 (andb3 true true false) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (* ================================================================= *)
  (** ** Types *)
  
  (** Every expression in Coq has a type, describing what sort of
      thing it computes. The [Check] command asks Coq to print the type
      of an expression. *)
  
  Check true.
  (* ===> true : bool *)
  
  (** If the expression after [Check] is followed by a colon and a type,
      Coq will verify that the type of the expression matches the given
      type and halt with an error if not. *)
  
  Check true
    : bool.
  Check (negb true)
    : bool.
  
  (** Functions like [negb] itself are also data values, just like
      [true] and [false].  Their types are called _function types_, and
      they are written with arrows. *)
  
  Check negb
    : bool -> bool.
  
  (** The type of [negb], written [bool -> bool] and pronounced
      "[bool] arrow [bool]," can be read, "Given an input of type
      [bool], this function produces an output of type [bool]."
      Similarly, the type of [andb], written [bool -> bool -> bool], can
      be read, "Given two inputs, each of type [bool], this function
      produces an output of type [bool]." *)
  
  (* ================================================================= *)
  (** ** New Types from Old *)
  
  (** The types we have defined so far are examples of "enumerated
      types": their definitions explicitly enumerate a finite set of
      elements, called _constructors_.  Here is a more interesting type
      definition, where one of the constructors takes an argument: *)
  
  Inductive rgb : Type :=
    | red
    | green
    | blue.
  
  Inductive color : Type :=
    | black
    | white
    | primary (p : rgb).
  
  (** Let's look at this in a little more detail.
  
      An [Inductive] definition does two things:
  
      - It defines a set of new _constructors_. E.g., [red],
        [primary], [true], [false], [monday], etc. are constructors.
  
      - It groups them into a new named type, like [bool], [rgb], or
        [color].
  
      _Constructor expressions_ are formed by applying a constructor
      to zero or more other constructors or constructor expressions,
      obeying the declared number and types of the constructor arguments.
      E.g.,
          - [red]
          - [true]
          - [primary red]
          - etc.
      But not
          - [red primary]
          - [true red]
          - [primary (primary red)]
          - etc.
  *)
  
  (** In particular, the definitions of [rgb] and [color] say
      which constructor expressions belong to the sets [rgb] and
      [color]:
  
      - [red], [green], and [blue] belong to the set [rgb];
      - [black] and [white] belong to the set [color];
      - if [p] is a constructor expression belonging to the set [rgb],
        then [primary p] (pronounced "the constructor [primary] applied
        to the argument [p]") is a constructor expression belonging to
        the set [color]; and
      - constructor expressions formed in these ways are the _only_ ones
        belonging to the sets [rgb] and [color]. *)
  
  (** We can define functions on colors using pattern matching just as
      we did for [day] and [bool]. *)
  
  Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.
  
  (** Since the [primary] constructor takes an argument, a pattern
      matching [primary] should include either a variable (as above --
      note that we can choose its name freely) or a constant of
      appropriate type (as below). *)
  
  Definition isred (c : color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.
  
  (** The pattern "[primary _]" here is shorthand for "the constructor
      [primary] applied to any [rgb] constructor except [red]."  (The
      wildcard pattern [_] has the same effect as the dummy pattern
      variable [p] in the definition of [monochrome].) *)
  
  (* ================================================================= *)
  (** ** Modules *)
  
  (** Coq provides a _module system_ to aid in organizing large
      developments.  We won't need most of its features,
      but one is useful: If we enclose a collection of declarations
      between [Module X] and [End X] markers, then, in the remainder of
      the file after the [End], these definitions are referred to by
      names like [X.foo] instead of just [foo].  We will use this
      feature to limit the scope of definitions, so that we are free to
      reuse names. *)
  
  Module Playground.
    Definition b : rgb := blue.
  End Playground.
  
  Definition b : bool := true.
  
  Check Playground.b : rgb.
  Check b : bool.
  
  (* ================================================================= *)
  (** ** Tuples *)
  
  Module TuplePlayground.
  
  (** A single constructor with multiple parameters can be used
      to create a tuple type. As an example, consider representing
      the four bits in a nybble (half a byte). We first define
      a datatype [bit] that resembles [bool] (using the
      constructors [B0] and [B1] for the two possible bit values)
      and then define the datatype [nybble], which is essentially
      a tuple of four bits. *)
  
  Inductive bit : Type :=
    | B0
    | B1.
  
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  
  Check (bits B1 B0 B1 B0)
    : nybble.
  
  (** The [bits] constructor acts as a wrapper for its contents.
      Unwrapping can be done by pattern-matching, as in the [all_zero]
      function which tests a nybble to see if all its bits are [B0].  We
      use underscore (_) as a _wildcard pattern_ to avoid inventing
      variable names that will not be used. *)
  
  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
  
  Compute (all_zero (bits B1 B0 B1 B0)).
  (* ===> false : bool *)
  Compute (all_zero (bits B0 B0 B0 B0)).
  (* ===> true : bool *)
  
  End TuplePlayground.
  
  (* ================================================================= *)
  (** ** Numbers *)
  
  (** We put this section in a module so that our own definition of
      natural numbers does not interfere with the one from the
      standard library.  In the rest of the book, we'll want to use
      the standard library's. *)
  
  Module NatPlayground.
  
  (** All the types we have defined so far -- both "enumerated
      types" such as [day], [bool], and [bit] and tuple types such as
      [nybble] built from them -- are finite.  The natural numbers, on
      the other hand, are an infinite set, so we'll need to use a
      slightly richer form of type declaration to represent them.
  
      There are many representations of numbers to choose from. We are
      most familiar with decimal notation (base 10), using the digits 0
      through 9, for example, to form the number 123.  You may have
      encountered hexadecimal notation (base 16), in which the same
      number is represented as 7B, or octal (base 8), where it is 173,
      or binary (base 2), where it is 1111011. Using an enumerated type
      to represent digits, we could use any of these as our
      representation natural numbers. Indeed, there are circumstances
      where each of these choices would be useful.
  
      The binary representation is valuable in computer hardware because
      the digits can be represented with just two distinct voltage
      levels, resulting in simple circuitry. Analogously, we wish here
      to choose a representation that makes _proofs_ simpler.
  
      In fact, there is a representation of numbers that is even simpler
      than binary, namely unary (base 1), in which only a single digit
      is used (as our ancient forebears might have done to count days by
      making scratches on the walls of their caves). To represent unary
      numbers with a Coq datatype, we use two constructors. The
      capital-letter [O] constructor represents zero.  When the [S]
      constructor is applied to the representation of the natural number
      n, the result is the representation of n+1, where [S] stands for
      "successor" (or "scratch").  Here is the complete datatype
      definition. *)
  
  Inductive nat : Type :=
    | O
    | S (n : nat).
  
  (** With this definition, 0 is represented by [O], 1 by [S O],
      2 by [S (S O)], and so on. *)
  
  (** Informally, the clauses of the definition can be read:
        - [O] is a natural number (remember this is the letter "[O],"
          not the numeral "[0]").
        - [S] can be put in front of a natural number to yield another
          one -- if [n] is a natural number, then [S n] is too. *)
  
  (** Again, let's look at this in a little more detail.  The definition
      of [nat] says how expressions in the set [nat] can be built:
  
      - the constructor expression [O] belongs to the set [nat];
      - if [n] is a constructor expression belonging to the set [nat],
        then [S n] is also a constructor expression belonging to the set
        [nat]; and
      - constructor expressions formed in these two ways are the only
        ones belonging to the set [nat]. *)
  
  (** These conditions are the precise force of the [Inductive]
      declaration.  They imply that the constructor expression [O], the
      constructor expression [S O], the constructor expression [S (S
      O)], the constructor expression [S (S (S O))], and so on all
      belong to the set [nat], while other constructor expressions, like
      [true], [andb true false], [S (S false)], and [O (O (O S))] do
      not.
  
      A critical point here is that what we've done so far is just to
      define a _representation_ of numbers: a way of writing them down.
      The names [O] and [S] are arbitrary, and at this point they have
      no special meaning -- they are just two different marks that we
      can use to write down numbers (together with a rule that says any
      [nat] will be written as some string of [S] marks followed by an
      [O]).  If we like, we can write essentially the same definition
      this way: *)
  
  Inductive nat' : Type :=
    | stop
    | tick (foo : nat').
  
  (** The _interpretation_ of these marks comes from how we use them to
      compute. *)
  
  (** We can do this by writing functions that pattern match on
      representations of natural numbers just as we did above with
      booleans and days -- for example, here is the predecessor
      function: *)
  
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  
  (** The second branch can be read: "if [n] has the form [S n']
      for some [n'], then return [n']."  *)
  
  (** The following [End] command closes the current module, so
      [nat] will refer back to the type from the standard library. *)
  
  End NatPlayground.
  
  (** Because natural numbers are such a pervasive form of data,
      Coq provides a tiny bit of built-in magic for parsing and printing
      them: ordinary decimal numerals can be used as an alternative to
      the "unary" notation defined by the constructors [S] and [O].  Coq
      prints numbers in decimal form by default: *)
  
  Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
  
  Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.
  
  Compute (minustwo 4).
  (* ===> 2 : nat *)
  
  (** The constructor [S] has the type [nat -> nat], just like functions
      such as [pred] and [minustwo]: *)
  
  Check S        : nat -> nat.
  Check pred     : nat -> nat.
  Check minustwo : nat -> nat.
  
  (** These are all things that can be applied to a number to yield a
      number.  However, there is a fundamental difference between [S]
      and the other two: functions like [pred] and [minustwo] are
      defined by giving _computation rules_ -- e.g., the definition of
      [pred] says that [pred 2] can be simplified to [1] -- while the
      definition of [S] has no such behavior attached.  Although it is
      _like_ a function in the sense that it can be applied to an
      argument, it does not _do_ anything at all!  It is just a way of
      writing down numbers.
  
      (Think about standard decimal numerals: the numeral [1] is not a
      computation; it's a piece of data.  When we write [111] to mean
      the number one hundred and eleven, we are using [1], three times,
      to write down a concrete representation of a number.)
  
      Now let's go on and define some more functions over numbers.
  
      For most interesting computations involving numbers, simple
      pattern matching is not enough: we also need recursion.  For
      example, to check that a number [n] is even, we may need to
      recursively check whether [n-2] is even.  Such functions are
      introduced with the keyword [Fixpoint] instead of [Definition]. *)
  
  Fixpoint even (n:nat) : bool :=
    match n with
    | O        => true
    | S O      => false
    | S (S n') => even n'
    end.
  
  (** We could define [odd] by a similar [Fixpoint] declaration, but
      here is a simpler way: *)
  
  Definition odd (n:nat) : bool :=
    negb (even n).
  
  Example test_odd1:    odd 1 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_odd2:    odd 4 = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** (You may notice if you step through these proofs that
      [simpl] actually has no effect on the goal -- all of the work is
      done by [reflexivity].  We'll discuss why that is shortly.)
  
      Naturally, we can also define multi-argument functions by
      recursion.  *)
  
  Module NatPlayground2.
  
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  
  (** Adding three to two now gives us five, as we'd expect. *)
  
  Compute (plus 3 2).
  (* ===> 5 : nat *)
  
  (** The steps of simplification that Coq performs can be
      visualized as follows: *)
  
  (*      [plus 3 2]
     i.e. [plus (S (S (S O))) (S (S O))]
      ==> [S (plus (S (S O)) (S (S O)))]
            by the second clause of the [match]
      ==> [S (S (plus (S O) (S (S O))))]
            by the second clause of the [match]
      ==> [S (S (S (plus O (S (S O)))))]
            by the second clause of the [match]
      ==> [S (S (S (S (S O))))]
            by the first clause of the [match]
     i.e. [5]  *)
  
  (** As a notational convenience, if two or more arguments have
      the same type, they can be written together.  In the following
      definition, [(n m : nat)] means just the same as if we had written
      [(n : nat) (m : nat)]. *)
  
  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity.  Qed.
  
  (** You can match two expressions at once by putting a comma
      between them: *)
  
  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
    end.
  
  End NatPlayground2.
  
  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
  
  (** **** Exercise: 1 star, standard (factorial)
  
      Recall the standard mathematical factorial function:
  
         factorial(0)  =  1
         factorial(n)  =  n * factorial(n-1)     (if n>0)
  
      Translate this into Coq.
  
      Make sure you put a [:=] between the header we've given you and
      your definition.  If you see an error like "The reference
      factorial was not found in the current environment," it means
      you've forgotten the [:=]. *)
  
  Fixpoint factorial (n:nat) : nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_factorial1:          (factorial 3) = 6.
  (* FILL IN HERE *) Admitted.
  Example test_factorial2:          (factorial 5) = (mult 10 12).
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** Again, we can make numerical expressions easier to read and write
      by introducing notations for addition, multiplication, and
      subtraction. *)
  
  Notation "x + y" := (plus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x - y" := (minus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x * y" := (mult x y)
                         (at level 40, left associativity)
                         : nat_scope.
  
  Check ((0 + 1) + 1) : nat.
  
  (** (The [level], [associativity], and [nat_scope] annotations
      control how these notations are treated by Coq's parser.  The
      details are not important for present purposes, but interested
      readers can refer to the "More on Notation" section at the end of
      this chapter.)
  
      Note that these declarations do not change the definitions we've
      already made: they are simply instructions to the Coq parser to
      accept [x + y] in place of [plus x y] and, conversely, to the Coq
      pretty-printer to display [plus x y] as [x + y]. *)
  
  (** When we say that Coq comes with almost nothing built-in, we really
      mean it: even equality testing is a user-defined operation!
      Here is a function [eqb], which tests natural numbers for
      [eq]uality, yielding a [b]oolean.  Note the use of nested
      [match]es (we could also have used a simultaneous match, as we did
      in [minus].) *)
  
  Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.
  
  (** Similarly, the [leb] function tests whether its first argument is
      less than or equal to its second argument, yielding a boolean. *)
  
  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.
  
  Example test_leb1:                leb 2 2 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_leb2:                leb 2 4 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_leb3:                leb 4 2 = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** We'll be using these (especially [eqb]) a lot, so let's give
      them infix notations. *)
  
  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
  
  Example test_leb3': (4 <=? 2) = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** We now have two symbols that look like equality: [=] and
      [=?].  We'll have much more to say about the differences and
      similarities between them later. For now, the main thing to notice
      is that [x = y] is a logical _claim_ -- a "proposition" -- that we
      can try to prove, while [x =? y] is an _expression_ whose
      value (either [true] or [false]) we can compute. *)
  
  (** **** Exercise: 1 star, standard (ltb)
  
      The [ltb] function tests natural numbers for [l]ess-[t]han,
      yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
      this one, define it in terms of a previously defined
      function.  (It can be done with just one previously defined
      function, but you can use two if you want.) *)
  
  Definition ltb (n m : nat) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
  
  Example test_ltb1:             (ltb 2 2) = false.
  (* FILL IN HERE *) Admitted.
  Example test_ltb2:             (ltb 2 4) = true.
  (* FILL IN HERE *) Admitted.
  Example test_ltb3:             (ltb 4 2) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (* ################################################################# *)
  (** * Proof by Simplification *)
  
  (** Now that we've defined a few datatypes and functions, let's
      turn to stating and proving properties of their behavior.
      Actually, we've already started doing this: each [Example] in the
      previous sections makes a precise claim about the behavior of some
      function on some particular inputs.  The proofs of these claims
      were always the same: use [simpl] to simplify both sides of the
      equation, then use [reflexivity] to check that both sides contain
      identical values.
  
      The same sort of "proof by simplification" can be used to prove
      more interesting properties as well.  For example, the fact that
      [0] is a "neutral element" for [+] on the left can be proved just
      by observing that [0 + n] reduces to [n] no matter what [n] is -- a
      fact that can be read directly off the definition of [plus]. *)
  
  Theorem plus_O_n : forall n : nat, 0 + n = n.
  Proof.
    intros n. simpl. reflexivity.  Qed.
  
  (** (You may notice that the above statement looks different in
      the [.v] file in your IDE than it does in the HTML rendition in
      your browser. In [.v] files, we write the universal quantifier
      [forall] using the reserved identifier "forall."  When the [.v]
      files are converted to HTML, this gets transformed into the
      standard upside-down-A symbol.)
  
      This is a good place to mention that [reflexivity] is a bit more
      powerful than we have acknowledged. In the examples we have seen,
      the calls to [simpl] were actually not needed, because
      [reflexivity] can perform some simplification automatically when
      checking that two sides are equal; [simpl] was just added so that
      we could see the intermediate state -- after simplification but
      before finishing the proof.  Here is a shorter proof of the
      theorem: *)
  
  Theorem plus_O_n' : forall n : nat, 0 + n = n.
  Proof.
    intros n. reflexivity. Qed.
  
  (** Moreover, it will be useful to know that [reflexivity] does
      somewhat _more_ simplification than [simpl] does -- for example,
      it tries "unfolding" defined terms, replacing them with their
      right-hand sides.  The reason for this difference is that, if
      reflexivity succeeds, the whole goal is finished and we don't need
      to look at whatever expanded expressions [reflexivity] has created
      by all this simplification and unfolding; by contrast, [simpl] is
      used in situations where we may have to read and understand the
      new goal that it creates, so we would not want it blindly
      expanding definitions and leaving the goal in a messy state.
  
      The form of the theorem we just stated and its proof are almost
      exactly the same as the simpler examples we saw earlier; there are
      just a few differences.
  
      First, we've used the keyword [Theorem] instead of [Example].
      This difference is mostly a matter of style; the keywords
      [Example] and [Theorem] (and a few others, including [Lemma],
      [Fact], and [Remark]) mean pretty much the same thing to Coq.
  
      Second, we've added the quantifier [forall n:nat], so that our
      theorem talks about _all_ natural numbers [n].  Informally, to
      prove theorems of this form, we generally start by saying "Suppose
      [n] is some number..."  Formally, this is achieved in the proof by
      [intros n], which moves [n] from the quantifier in the goal to a
      _context_ of current assumptions. Note that we could have used
      another identifier instead of [n] in the [intros] clause, (though
      of course this might be confusing to human readers of the proof): *)
  
  Theorem plus_O_n'' : forall n : nat, 0 + n = n.
  Proof.
    intros m. reflexivity. Qed.
  
  (** The keywords [intros], [simpl], and [reflexivity] are examples of
      _tactics_.  A tactic is a command that is used between [Proof] and
      [Qed] to guide the process of checking some claim we are making.
      We will see several more tactics in the rest of this chapter and
      many more in future chapters. *)
  
  (** Other similar theorems can be proved with the same pattern. *)
  
  Theorem plus_1_l : forall n:nat, 1 + n = S n.
  Proof.
    intros n. reflexivity.  Qed.
  
  Theorem mult_0_l : forall n:nat, 0 * n = 0.
  Proof.
    intros n. reflexivity.  Qed.
  
  (** The [_l] suffix in the names of these theorems is
      pronounced "on the left." *)
  
  (** It is worth stepping through these proofs to observe how the
      context and the goal change.  You may want to add calls to [simpl]
      before [reflexivity] to see the simplifications that Coq performs
      on the terms before checking that they are equal. *)
  
  (* ################################################################# *)
  (** * Proof by Rewriting *)
  
  (** The following theorem is a bit more interesting than the
      ones we've seen: *)
  
  Theorem plus_id_example : forall n m:nat,
    n = m ->
    n + n = m + m.
  
  (** Instead of making a universal claim about all numbers [n] and [m],
      it talks about a more specialized property that only holds when
      [n = m].  The arrow symbol is pronounced "implies."
  
      As before, we need to be able to reason by assuming we are given such
      numbers [n] and [m].  We also need to assume the hypothesis
      [n = m]. The [intros] tactic will serve to move all three of these
      from the goal into assumptions in the current context.
  
      Since [n] and [m] are arbitrary numbers, we can't just use
      simplification to prove this theorem.  Instead, we prove it by
      observing that, if we are assuming [n = m], then we can replace
      [n] with [m] in the goal statement and obtain an equality with the
      same expression on both sides.  The tactic that tells Coq to
      perform this replacement is called [rewrite]. *)
  
  Proof.
    (* move both quantifiers into the context: *)
    intros n m.
    (* move the hypothesis into the context: *)
    intros H.
    (* rewrite the goal using the hypothesis: *)
    rewrite -> H.
    reflexivity.  Qed.
  
  (** The first line of the proof moves the universally quantified
      variables [n] and [m] into the context.  The second moves the
      hypothesis [n = m] into the context and gives it the name [H].
      The third tells Coq to rewrite the current goal ([n + n = m + m])
      by replacing the left side of the equality hypothesis [H] with the
      right side.
  
      (The arrow symbol in the [rewrite] has nothing to do with
      implication: it tells Coq to apply the rewrite from left to right.
      In fact, you can omit the arrow, and Coq will default to rewriting
      in this direction.  To rewrite from right to left, you can use
      [rewrite <-].  Try making this change in the above proof and see
      what difference it makes.) *)
  
  (** **** Exercise: 1 star, standard (plus_id_exercise)
  
      Remove "[Admitted.]" and fill in the proof. *)


(* ここから記述 *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

