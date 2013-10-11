#!/usr/bin/python
steps = {

'1a1': """
all A ( is_only_in_itself(A) | is_only_in_another(A) ).
""",

# Note: the "exists" of predicate logic is not the "is" of Spinoza's
# philosophy. I am having trouble explaining how I use prover9's "exists",
# then. This could be a sign that Spinoza's philosophy is ultimately not
# translatable into a contemporary predicate logic, which has too many
# contemporary assumptions built into it. Perhaps what could be said in defense
# of this project is that it will make plainer---in the things that couldn't be
# captured--exactly where Spinoza departs from today's "common sense".

'1a4': """

all e all c (
        % if c causes e...
        causes(c, e) ->
        % ...then...
        (
            % ...there is a cognition of the effect that depends on and
            % involves the cognition of its cause.
            exists cog_e exists cog_c (
                is_cognition_of(cog_e, e) &
                is_cognition_of(cog_c, c) &
                depends_on(cog_e, cog_c) &
                involves(cog_e, cog_c)
            )
        )
    ).

""",

# 1a5: Things that have nothing in common with one another also cannot be
# understood through one another, or the concept of the one does not involve
# the concept of the other.

'1a5': """

all a all b (
    % If two things have nothing in common with one another...
    -(exists t ( has(a, t) & has(b, t) ))

    % ...then....
    ->

    (
        neither_is_understood_through_the_other(a, b)
        & the_concept_of_the_one_does_not_involve_the_concept_of_the_other(a, b)
    )
).
""",

# Note that this claim---"Things have have nothing in common with one
# another..."---is a generic, which I am interpreting as two universal
# quantifiers.

# I take "cannot" to mean "ipso facto not".

# 1a7: If a thing can be conceived as not existing, its essence does
# not involve existence.

'1a7': """

    all X (
        conceivably_does_not_exist(X)
        ->
        -essence_involves_existence(X)
    ).

""",

# Definition of causa sui
'1def1': """

    all X (
        causes(X,X) <-> essence_involves_existence(X)
    ).

""",

# 1def3: By substance I understand what is in itself and is conceived
# through itself, i.e., that whose concept does not require the concept of
# another thing, from which it must be formed.

'1def3': """

    all S (
        is_substance(S) <-> (
            % S is the only thing it is in
            all T ( is_in(S,T) <-> (S=T) )
        )
    ).

    all S (
        is_substance(S) <-> (
            all T ( is_conceived_through(S,T) <-> (S=T) )
            % &
            % % It's not the case that...
            % -(
            %     exists sc exists t exists tc (
            %     % ...any concept of the substance...
            %     is_concept_of(tc,c) &
            %     % ...requires any concept...
            %     requires(sc,tc) &
            %     is_concept_of(sc,s) &
            %     % ...of a distinct thing.
            %     -(s=t)
            %     )
            % )
        )
    ).

    % The definition seems to be used in this way too.
    all S (
        is_substance(S) <-> is_in(S,S)
    ).

    % TODO: Because this is a real definition, it states not only the
    % biconditional, but also that the biconditional makes plain the essence of
    % the thing. I'm not sure how to write that in prover9.

    % TODO: Haven't encoded the "I understand" bit.

""",

# 1def4: By attribute I understand what the intellect perceives of a substance,
# as constituting its essence.

'1def4': """

    % Will leave this blank and try to fill in in various ways.

""",

# 1def5: By mode I understand the affections of a substance, or that which is
# in another through which it is also conceived.

'1def5': """

    all M (
        is_mode(M) -> (
            exists S (
                is_substance(S) &
                is_mode_of(M, S) &
                is_in(M, S) &
                is_conceived_through(M, S)
            )
        )
    ).

    all M all S (
        ( is_mode(M) & is_mode_of(M, S) & is_substance(S) )
        ->
        (is_in(M, S) & is_conceived_through(M, S))
    ).

    all M ( ( exists S ( is_in(M, S) ) ) -> is_mode_of(M, S) ).

    % TODO: Haven't encoded the "I understand" bit.

""",

# 1def6: By God I understand a being absolutely infinite, i.e., a substance
# consisting of an infinity of attributes, of which each one expresses an
# eternal and infinite essence.

'1def6': """

    % God is a substance.
    is_substance(God).

    % God has all the attributes.
    all A ( is_attribute(A) -> ( exists G ( God=G & is_attribute_of(A,G) ) ) ).

    % Each attribute of God expresses an eternal and infinite essence.
    all A (
        is_attribute_of(A, God)
        ->
        exists E (
            is_essence(E) &
            expresses(A,E) &
            is_eternal(E) &
            is_infinite(E)
        )
    ).

""",

# 1def8: By eternity I understand existence itself, insofar as it is conceived
# to follow necessarily from the definition alone of the eternal thing.

'1def8': """

    % Paraphrasing this as something like: if the existence of something
    % follows from its definition then its existence is eternity.
    all x (follows_from(existence(x),definition(x)) -> (existence(x) = Eternity)).

    % TODO: Incorporate the "insofar as" bit.

""",

'1p1': """

    % 1p1: A substance is prior in nature to its affections.
    all S all A (
        ( is_substance(S) & is_affection_of(A, S) )
        ->
        is_prior_in_nature_to(S, A)
    ).

    % Noticed while doing this: This proposition is ambiguous between "a
    % substance is prior in nature to all of its affections taken together" and
    % "a substance is prior in nature to each of its affections."

    % Noticed while doing this: It's not clear why 1def3 is needed in the
    % demonstration.

""",

# 1p11: God, or a substance consisting of infinite attributes, each of
# which expresses eternal and infinite essence, necessarily exists.
#
# Dem.: If you deny this, conceive, if you can, that God does not
# exist.  Therefore (by 1a7) his essence does not involve existence.
# But this (by 1p7) is absurd. Therefore God necessarily exists, q.e.d.

'1p11': """

    % Treating existence like a predicate.
    necessarily_exists(God).

""",

# 1p14: Except God, no substance can be or be conceived.
# 
# Dem.: Since God is an absolutely infinite being, of whom no attribute which
# expresses an essence of substance can be denied (by 1def6), and he
# necessarily exists (by 1p11), if there were any substance except God, it
# would have to be explained through some attribute of God, and so two
# substances of the same attribute would exist, which (by 1p5) is absurd.  And
# so except God, no substance can be or, consequently, be conceived.  For if it
# could be conceived, it would have to be conceived as existing.  But this (by
# the first part of this demonstration) is absurd. Therefore, except for God no
# substance can be or be conceived, q.e.d.

'1p14': """

    % Except God, no substance can be or be conceived.
    all s ( is_substance(s) -> (s=God) ).

""",

# 1p15: Whatever is, is in God, and nothing can be or be conceived without God.
#
# Dem.: Except for God, there neither is, nor can be conceived, any substance
# (by 1p14), i.e. (by 1def3), thing that is in itself and is conceived through
# itself.  But modes (by 1def5) can neither be nor be conceived without
# substance. So they can be in the divine nature alone, and can be conceived
# through it alone.  But except for substances and modes [II/57] there is
# nothing (by 1a1).  Therefore, [NS: everything is in God and] nothing can be
# or be conceived without God, q.e.d.

'1p15': """

    all X ( is_in(X,God) ). %& -can_be_without(X,God) & -can_be_conceived_without(God) ).

""",

# 1p16: From the necessity of the divine nature there must follow infinitely
# many things in infinitely many modes, (i.e., everything which can fall under
# an infinite intellect.)
# 
# Dem.: This Proposition must be plain to anyone, provided he attends to the
# fact that the intellect infers from the given definition of any thing a
# number of properties that really do follow necessarily from it (i.e., from
# the very essence of the thing); and that it infers more properties the more
# the definition of the thing expresses reality, i.e., the more reality the
# essence of the defined thing involves. But since the divine nature has
# absolutely infinite attributes (by 1def6), each of which also expresses an
# essence infinite in its own kind, from its necessity there must follow
# infinitely many things in infinite modes (i.e., everything which can fall
# under an infinite intellect), q.e.d.

'1p16': """

    % The number of modes of each attribute is infinite.
    %all a ( is_attribute(a) -> number(modes_of(a), Infinity) ).
    exists properties (
        (properties = modes_of(God)) &
        (a_infers_b_from_c(Intellect, properties, definition(God))) &
        infinite(properties)
    ).

    % All modes follow from the divine nature.

    %number(DivineAttributes, Infinity).

    all m ( is_mode(m) -> follows_from(m, DivineNature) ).

""",

'1p19': """
    % 1p19: God is eternal, or all God's attributes are eternal.
    eternal(God).
""",

'1p2': """
% 1p2: Two substances having different attributes have nothing in common with
% one another.
%
% Dem.: This also evident from 1def3. For each must be in itself and be
% conceived through itself, or the concept of the one does not involve the
% concept of the other.

    all s1 all s2 (

        % If there are two substances...
        ( is_substance(s1) & is_substance(s2) & -(s1=s2) )

        % ...then...
        ->

        % ...there is no attribute they have in common.
        -( exists a ( is_attribute_of(a, s1) & is_attribute_of(a, s2) ) )

    ).

""",

# 1p21: All the things which follow from the absolute nature of any of God's
# attributes have always had to exist and be infinite, or are, through the same
# attribute, eternal and infinite.

'1p21': """

    % 1p21: All the things which follow from the absolute nature of any of God's
    % attributes
    all t (
        (
            % simplify for now
            follows_from(t, God)
            %exists nature exists a (
            %    is_attribute_of(a, God) &
            %    is_absolute_nature_of(nature, a) &
            %    follows_from(t, nature)
            %)
        )
        ->
        % have always had to exist and be infinite, or are, through the same
        % attribute, eternal and infinite.
        (
            is_infinite(t)
            %has_always_existed(t) & has_always_been_infinite(t) &
            %eternal_through(t, a) &
            %infinite_through(t, a)
        )
    ).

""",

'1p22': """

    % 1p22: Whatever follows from some attribute of God
    % insofar as it is modified by a modification which,
    % through the same attribute, exists necessarily and
    % is infinite, must also exist necessarily and be
    % infinite.

    % Whatever follows from some attribute of God insofar as it is modified by
    % a modification which, through the same attribute, exists necessarily and
    % is infinite
    all x exists mod exists attribute (
        (
            % Note simplification here: to follow from an attribute insofar as
            % it is modified is to follow from a modification of that attribute
            follows_from(x, mod) &
            is_modification_of(mod, attribute) &
            exists_necessarily(mod) &
            is_infinite(mod)
        )
        ->
        (
            exists_necessarily(x) & is_infinite(x)
        )
    ).

""",

# 1p24: The essence of things produced by God does not involve
# existence.
'1p24': """

    % The phrase 'things produced by God' implicitly excludes
    % God.
    all x (
        (produced_by(x,God) & -(God=x))
        ->
        -essence_involves_existence(x)
    ).

""",

# 1p24c: From this it follows that God is not only the cause of things'
# beginning to exist, but also of their persevering in existing, *or* (to use a
# Scholastic term) God is the cause of the being of things.  For -- whether the
# things [NS: produced] exist or not -- so long as we attend to their essence,
# we shall find that it involves neither existence nor duration. So their
# essence can be the cause neither of their existence nor of their duration,
# but only God, to whose nature alone it pertains to exist[, can be the cause]
# (by 1p14c1).

'1p24c': """
    % God is...the cause of things' persevering in existing.
    all t exists b ( is_being_of(b, t) & partial_cause(God, b) ).

    % Noticed while doing this: we can't translate this as "God is *the* cause
    % of the being of things" because there are other causes. So we must
    % translate it as "God is a cause"

""",

# 1p25c: Particular things are nothing but affections of God's attributes, *or*
# modes by which God's attributes are expressed in a certain and determinate
# way.  The demonstration is evident from 1p15 and 1def5.

'1p25c': """

    % Paraphrasing as: each particular thing is nothing but an affection of an
    % attribute of God and this affection is a mode that expresses an attribute
    % of God.
    all t (
        is_particular_thing(t) ->
        (
            exists attribute exists affection (
                is_nothing_but(t, affection) &
                is_affection_of(affection, attribute) &
                is_attribute_of(attribute, God)
            )
            &
            is_mode(affection)
            &
            expresses_in_a_certain_and_determinate_way(affection, attribute)
        )
    ).

""",

# 1p26: A thing which has been determined to produce an effect has necessarily
# been determined in this way by God; and one which has not been determined by
# God cannot determine itself to produce an effect.

'1p26': """

    % Simplification: doesn't subselect things in particular
    all t (
        (exists e (determined_to_produce(t, e)))
        ->
        x_determines_y_to_produce_z(God, t, e)
    ).

""",

# 1p28: Every singular thing, or any thing which is finite and has a
# determinate existence, can neither exist nor be determined to produce an
# effect unless it is determined to exist and produce an effect by another
# cause, which is also finite and has a determinate existence; and again, this
# cause also can neither exist nor be determined to produce an effect unless it
# is determined to exist and produce an effect by another, which is also finite
# and has a determinate existence, and so on, to infinity.

'1p28': """

    %all x (is_finite(x) -> exists y (causes(y,x))).
    %all x all y ((causes(x,y) & infinite(x)) -> infinite(y)).
    all x (infinite(x)).
    % For simplicity, ignoring "exists" and just handling "determined to exist"
    %all y (
    %    % Every singular thing, or any thing which is finite and has a
    %    % determinate existence,
    %    (
    %        %is_singular(y) &
    %        is_finite(y) &
    %        %has_determinate_existence(y) &
    %        %determined_to_produce_effect(y)
    %    )
    %    % can neither exist nor be determined to produce an
    %    % effect unless
    %    ->
    %    % it is determined to exist and produce an effect by another cause,
    %    % which is also finite and has a determinate existence;
    %    (
    %        exists x ( %exists z 
    %            is_infinite(x) %determines_to_exist(x, y) &
    %            %x_determines_y_to_produce_z(x, y, z) &
    %            %is_finite(x) %&
    %            %has_determinate_existence(x)
    %        )
    %    )
    %).

""",

# intermediary step on the way to 1p28
'1p28-i': """

    all x (
        is_finite(x) -> -causes(God, x)
    ).

""",

'1p2': """
% 1p2: Two substances having different attributes have nothing in common with
% one another.
%
% Dem.: This also evident from 1def3. For each must be in itself and be
% conceived through itself, or the concept of the one does not involve the
% concept of the other.

    all s1 all s2 (

        % If there are two substances with different attributes...
        (
            ( is_substance(s1) & is_substance(s2) & -(s1=s2) )
            & -exists a ( is_attribute_of(a, s1) && is_attribute_of(a, s2) )
        )

        % ...then...
        ->

        % ...there is no thing that each has.
        -exists t ( has(s1, t) && has(s2, t) )

    ).
""",

'1p3': """

% 1p3: If things have nothing in common with one another, one of them cannot be
% the cause of the other.
%
% Dem.: If they have nothing in common with one another, then (by 1a5) they
% cannot be understood through one another, and so (by 1a4) one cannot be the
% cause of the other, q.e.d.

% Used in 1p6

    % Given two things,
    all a all b (

        % If there is no thing that they both have, ...
        -(exists t ( has(a, t) & has(b, t) ))

        % ...then...
        ->

        % ...neither is understood through nor causes the other.
        (
            neither_is_understood_through_the_other(a, b)
            &
            neither_causes_the_other(a, b)
        )
    ).

% Note that "they cannot be understood through one another" must mean "neither
% can be understood through the another", although strictly speaking it could
% mean that it is impossible to (simultaneously?) understand each through the
% other.

""",

'1p4': """

% 1p4: Two or more distinct things are distinguished from one another, either
% by a difference in the attributes of the substances or by a difference in
% their affections.
% 
% Dem.: Whatever is, is either in itself or in another (by 1a1), i.e. (by 1def3
% and 1def5), outside the intellect there is nothing except substances and
% their affections. Therefore, there is nothing outside the intellect through
% which a number of things can be distinguished from one another except
% substances, or what is the same (by 1def4), their attributes, and their
% affections, q.e.d.

    % For simplicity, I will just stick to two things.
    % all a all b all c (
    %     distinguished_by(a, b, c)
    %     ->
    %     (
    %         (
    %             is_a_difference_in_attributes(c, a, b)
    %             & is_substance(a)
    %             & is_substance(b)
    %         )
    %         |
    %         is_a_difference_in_affections(c, a, b)
    %     )
    % ).

    % Paraphrase: For any distinct x and y, there is either an attribute that
    % exactly one of them has, or an affection that exactly one of them has.
    all x all y (
        (
            -(x=y)
        )
        ->
        (
            exists a (
                ( is_attribute_of(a, x) & -is_attribute_of(a, y) )
                |
                ( -is_attribute_of(a, x) & is_attribute_of(a, y) )
                |
                ( is_affection_of(a, x) & -is_affection_of(a, y) )
                |
                ( -is_affection_of(a, x) & is_affection_of(a, y) )
            )
        )
    ).

""",

'1p5': """

% 1p5: In nature there cannot be two or more substances of the same
% nature or attribute.
% 
% Dem.: If there were two or more distinct substances, they would have
% to be distinguished from one another either by a difference in their
% attributes, or by a difference in their affections (by 1p4). If only
% by a difference in their attributes, then it will be conceded that
% there is only one of the same attribute. But if by a difference in
% their affections, then since a substance is prior in nature to its
% affections (by 1p1), if the affections are put to one side and [the
% substance] is considered in itself, i.e. (by 1def3 and 1a6),
% considered truly, one cannot be conceived to be distinguished from
% another, i.e. (by 1p4), there cannot be many, but only one [of the
% same nature or attribute], q.e.d.

% Rewriting the above.
all s all t all a (
    % If an attribute belongs to two substances...
    ( is_substance(s) & is_substance(t) & is_attribute_of(a, s) & is_attribute_of(a, t) )
    ->
    % ...then they are identical
    (s=t)
).
""",

'1p6': """

% 1p6: One substance cannot be produced by another substance.
%
% Dem.: In nature there cannot be two substances of the same attribute (by
% 1p5), i.e. (by 1p2), which have something in common with each other.
% Therefore (by 1p3) one cannot be the cause of the other, or cannot be
% produced by the other, q.e.d.

    all s (
        is_substance(s)
        ->
        -( exists s2 ( -(s=s2) & produces(s2, s) ) )
    ).

    % I'm hoping that the formula above could be written like this one day:
    % "For all s, if s is a substance, then it is not the case that there exists
    % something s2 such that s and s2 are distinct and s2 produces s."

""",

'1p7': """

% 1p7: It pertains to the nature of a substance to exist.
%
% Dem.: A substance cannot be produced by anything else (by 1p6c); therefore it
% will be the cause of itself, i.e. (by 1def1), its essence necessarily
% involves existence, or it pertains to its nature to exist, q.e.d.

    all s ( is_substance(s) -> pertains_to_its_nature_to_exist(s) ).

""",

'2a1': """

    % 2a1'' (G II/99)

    % "All modes by which a body is affected by another body follow both
    % from the nature of the body affected at at the same time from the
    % nature of the affecting body..."
    
    % I'm ignoring this bit, which I take to just be a gloss:

    % "so that one and the same body may be moved differently according to
    % differences in the nature of the bodies moving it. And conversely,
    % different bodies may be moved differently by one and the same body."

    all mode all body
    (
        (
            % All modes of any given body...
            mode_of(mode,body) &
            is_body(body) &
            % ...that have an external cause...
            exists body2 ( cause(body2,mode) & -(body2=body) )
        )
        -> % ...are such that...
        (
            all n all n2
            (
                (
                    % ...the nature of the affected body
                    nature_of(n,body) &
                    % ...and the nature of the affecting body
                    nature_of(n2,body2)
                )
                -> % ...are such that...
                (
                    % ...the mode follows from both natures.
                    follow_from(mode,n) & follow_from(mode,n2)
                )
            )
        )
    ).

""",

# 2p16: The idea of any mode in which the human body is affected by external
# bodies must involve the nature of the human body and at the same time the
# nature of the external body.
'2p16': """

    all mode all body (
        % for each mode of the human body...
        (
            is_human(body) &
            mode_of(mode,body)
        ) ->
        % ...all of that mode's external causes
        all body2 (
            ( cause(body2,mode) & -(body2 = body) )
            -> % are such that
            all i all n all n2 (
                % the idea of that mode involves the external bodies' natures
                ( idea_of(i,body) & nature_of(n,body) & nature_of(n2,body2) )
                ->
                ( involves(i,n) & involves(i,n2) )
            )
        )
    ).

""",

# 2p7: The order and connection of ideas is the same as the order and
# connection of things.

'2p7': """

    % Two ideas are connected (implicitly: by a relation of dependence)
    (
        exists i exists j
        (
            is_idea(i) &
            is_idea(j) &
            depends_on(j, i) 
        )
    )
    % ...if and only if two things are connected (implicitly: by a causal relation)
    <->
    (
        exists t exists u (
            causes(t, u)
        )
    ).

    % Noticed: this seems to require that causation, dependence and involvement are
    % the only ways of being connected.

""",

# Some of Spinoza's phrases involve
# generics. If we switch to a generic
# interpretation of them, what happens to
# the book?

"Assumption: Anything that's an idea of something is an idea":
"all I all O ( is_idea_of(I,O) -> is_idea(I) ).",

"Assumption: Anything that's a cognition of something is an idea of that thing.":
"all I all O ( is_cognition_of(I,O) <-> is_idea_of(I,O) ).",

"Assumption: Ideas are concepts":
"all I all X ( is_idea_of(I,X) <-> is_concept_of(I,X) ).",

"Assumption: Whatever we end up talking about is a 'thing'.":
"all X is_thing(X).",

"Assumption: There is an idea of each thing. (Needed for 2p7)":
"all T ( exists I ( is_idea_of(I, T) ) ).",

"Assumption: Definition of essential involvement":
"all X all F ( involves_essentially(X,F) <-> all E ( is_essence_of(E,X) -> involves(E,F) )).",

# We need either this or 'everything has a cause'
"Assumption: Everything is conceived through something":
"all X (exists Y conceived_through(X,Y)).",

"Everything has a cause":
"all X (exists Y causes(Y,X)).",

"To not conceivably have is to necessarily lack.":
"all X all F ( -conceivably_has(X,F) <-> necessarily_lacks(X,F) ).",

"To necessarily lack is to not possibly have":
"all X all F ( necessarily_lacks(X,F) <-> -possibly_has(X,F) ).",

"To conceivably lack is to not necessarily have":
"all X all F ( conceivably_lacks(X,F) <-> -necessarily_has(X,F) ).",

# Seemingly at least one of these is needed for 1p1
"What something is conceived through is prior in nature to it":
"all X all Y ( is_conceived_through(Y, X) -> is_prior_in_nature_to(X, Y) ).",

"What something is in is prior in nature to it":
"all X all Y ( is_in(Y, X) -> is_prior_in_nature_to(X, Y) ).",

"If A is an affection of S then A is an affection and S has A":
"all A all S ( is_affection_of(A, S) -> ( is_affection(A) & has(S, A) ) ).",

"If A is an attribute of S then A is an attribute and S has A":
"all A all S ( is_attribute_of(A, S) -> ( is_attribute(A) & has(S, A) ) ).",

"Assumption: Your modes are your affections":
"all X all Y ( is_mode_of(X,Y) <-> is_affection_of(X,Y) ).",

"Assumption: Modes are affections and vice versa":
"all X ( is_mode(X) <-> is_affection(X) ).",

"Assumption: Your modes are modes and you have them.":
"all X all Y ( is_mode_of(X,Y) <-> ( is_mode(X) & has(Y, X) ) ).",

"Assumption: If you're conceived through something then its concept involves your concept":
"""
    all X all Y (
        is_conceived_through(A, B)
        ->
        (
            exists CA exists CB (
                is_concept_of(CA, A) &
                is_concept_of(CB, B) &
                involves(CB, CA)
            )
        )
    ).
""",

"Assumption: Grammar of 'neither of two things is understood through the other'":
"""
all A all B (
    neither_is_understood_through_the_other(A, B)
    <->
    (
        -is_understood_through(A, B)
        & -is_understood_through(B, A)
    )
).
""",

"Assumption: Grammar of 'neither causes the other'":
"""
    all A all B (
        neither_causes_the_other(A, B)
        <->
        (
            -causes(A, B)
            & -causes(B, A)
        )
    ).
""",

"Assumption: Grammar of 'the concept of the one does not involve the concept of the other":
"""
    all A all B (
        the_concept_of_the_one_does_not_involve_the_concept_of_the_other(A, B)
        <->
        (
            all CA all CB (
                (
                    is_concept_of(CA, A)
                    & is_concept_of(CB, B)
                )
                ->
                (
                    -involves(CA, CB)
                    & -involves(CB, CA)
                )
            )
        )
    ).
""",

"Assumption: You are understood through your causes.":
"all A all B ( causes(A, B) -> is_understood_through(B, A) ). ",

"Assumption: What is understood through something is conceived through it":
"all A all B ( is_understood_through(A, B) <-> is_conceived_through(A, B) ).",

# This is to bring everything under the scope of 1a1
"Assumption: Everything is":
"all X ( is(X) ).",

    # Controversial but I think it's needed for 1p4. Talk of attributes is just
    # a way of talking about how a substance is conceived and it can be
    # regimented out.
"Assumption: Attributes are substances":
"all A ( is_attribute(A) <-> is_substance(A) ).",

"Assumption: What produces something causes it (but not necessarily vice versa)":
"all X all Y ( produces(X, Y) -> causes(X, Y)).",

"Assumption: If something is only in itself then anything it is in is actually itself":
"all A ( is_only_in_itself(A) <-> ( all B ( is_in(A,B) -> (B=A) ))).",

"Assumption: If something is only in another then it is not in itself but something else":
"""
all A (
    is_only_in_another(A)
    % better: is only in exactly one, distinct, thing
    <->
    (
        exists B ( -(B=A) & is_in(A,B) ) &
        -is_in(A,A)
    )
).
""",

"Assumption: A causes B iff B is in A":
"all A all B ( causes(A, B) <-> is_in(B, A) ).",

#all A all B ( -produces(A, B) ). % just for debugging 1p6
# If we write 2p7 in a way that involves the idea of a "connection", then we might need these.
# Each dependency relation is a "connection" in a graph.
#all X all Y ( depends_on(X,Y) <-> is_connected_to(X,Y) ).
#all X all Y ( depends_on(X,Y) <-> is_connected_to(Y,X) ). % perhaps?
#all X all Y ( involves(X,Y) <-> is_connected_to(X,Y) ).
#all X all Y ( involves(X,Y) <-> is_connected_to(Y,X) ). % perhaps?
#all X all Y ( causes(X,Y) <-> is_connected_to(X,Y) ).
#all X all Y ( causes(X,Y) <-> depends_on(Y,X) ). % perhaps?
#all X all Y ( is_connected_to(X,Y) -> causes(X,Y) ). % might make 2p7 work
#all X all Y ( is_connected_to(X,Y) -> ( causes(X,Y) | depends_on(X,Y) | involves(X,Y) ) ). % needed for 2p7?

"""Assumption: If it pertains to the nature of something to exist, then its
essence involves existence""":
"all S ( pertains_to_its_nature_to_exist(S) <-> essence_involves_existence(S) ).",

"""Assumption: If something does not conceivably fail to exist then it
necessarily exists""":
"all S ( -conceivably_does_not_exist(S) <-> necessarily_exists(S) ).",

"Assumption: If something necessarily exists then it necessarily has existence":
"all X ( necessarily_exists(X) <-> ( all E ( is_existence(E) -> necessarily_has(X, E) ) ) ).",

#Needed for 1p14.
"Assumption: Each substance has an attribute.":
"all S ( ( is_substance(S) & -is_attribute(S) ) -> ( exists A ( is_attribute_of(A, S) ) ) ).",

# I've included the clause `& -is_attribute(S)`, which is strictly speaking
# false. If we don't include it, this line combines with the formula stating
# that each attribute is a substance to produce an infinite loop.

"If an attribute belongs to two substances then they are identical":
"""
    % Rewriting the above.
    all S all T all A (
        % If an attribute belongs to two substances...
        ( is_substance(S) & is_substance(T) & is_attribute_of(A, S) & is_attribute_of(A, T) )
        ->
        % ...then they are identical
        (S = T)
    ).
""",

"Assumption: If there is a substance other than God then they do not share attributes":
"""
    exists S ( is_substance(S) & -(S=God) )
    ->
    exists S exists T exists A (
        -(S=T) & is_attribute_of(A,S) & is_attribute_of(A,T)
    ).
""",

#all X ( is_in(X,God) & -can_be_without(X,God) & -can_be_conceived_without(X,God) ).

"Assumption: Something cannot be without its causes":
"all X all Y ( causes(X,Y) -> -can_be_without(Y,X) ).",

"Assumption: Something cannot be conceived without what it is conceived through":
"all X all Y ( is_conceived_through(X,Y) -> -can_be_conceived_without(Y,X) ).",

# the intellect infers from the given definition of any thing a number of
# properties that really do follow necessarily from it (i.e., from the very
# essence of the thing); (1p16)

# "the intellect...infers more properties the more the definition of the
# thing expresses reality, i.e., the more reality the essence of the
# defined thing involves." (1p16)

# Paraphrase this as: if the definition of a thing expresses an infinite
# amount of reality, then the intellect infers an infinite number of
# properties from it.
"""Assumption: if the definition of a thing expresses an infinite amount of
reality, then the intellect infers an infinite number of properties from it.""":
"""
    all x (
        ( exists amount_of_reality (
            expresses(definition(x),amount_of_reality) &
            infinite(amount_of_reality)
        ))
        ->
        exists properties (
            (properties = modes_of(x)) &
            (a_infers_b_from_c(Intellect, properties, definition(x))) &
            infinite(properties)
        )
    ).
""",

"Assumption: the definition of God expresses an infinite amount of reality":
"""
    exists amount_of_reality (
        expresses(definition(God), amount_of_reality) &
        infinite(amount_of_reality)
    ).
""",


"""Assumption: If something expresses an infinite essence then the intellect
infers an infinite set of properties from it.""":
"""
    all x all y (
        (
            expresses(x,y) & is_essence_of(y,x) & infinite(y)
        )
        ->
        % ...then the intellect infers an infinite set of properties from it.
        exists properties (
            (properties = modes_of(x)) &
            (a_infers_b_from_c(Intellect, properties, definition(x))) &
            infinitely_large_set(properties)
        )
    ).
""",

"Assumption: any infinitely large set numbers infinity":
"all x (infinitely_large_set(x) <-> number(x, Infinity)).",

"Assumption: equivalence of is_infinite() and infinite()":
"all x (is_infinite(x) <-> infinite(x)).",

"Assumption: the existence of God follows from his definition":
"follows_from(existence(God),definition(God)).",

"Assumption: If the existence of something is eternity then it is eternal.":
"all x ((existence(x) = Eternity) -> eternal(x)).",

"Assumption: If B is produced by A, then A produces B":
"all A all B (produced_by(B, A) <-> produces(A, B)).",

"Assumption: The divine nature is the nature of God":
"is_the_nature_of(DivineNature, God).",

# Possibly incorrect.
"Assumption: If x is nothing but y, then x equals y":
"all x all y ( is_nothing_but(x,y) <-> x=y ).",

# Helps 1p25c go through.
"Assumption: A mode of a substance is a mode of one of its attributes.":
"""
    all M all S (
        is_mode_of(M, S)
        ->
        exists A (is_attribute_of(A, S) & is_mode_of(M, A))
    ).
""",

# Helps 1p25c to go through.
"""Assumption: If you express something you express it in a certain and
determinate way""":
"all x all y (expresses(x,y) -> expresses_in_a_certain_and_determinate_way(x,y)).",

"Assumption: Your modes express you":
"all x all y (is_mode_of(x,y) -> expresses(x,y)).",

# all x (has_always_existed(x) <-> sempiternal(x)).
# all x (has_always_been_infinite(x) <-> is_infinite(x)).

# all x all y (eternal_through(x, y) -> is_eternal(x)).
# all x all y (infinite_through(x, y) -> is_infinite(x)).

# all x ( is_finite(x) <-> -is_infinite(x) ).

"Assumption: what follows from something is caused by it":
"all x all y (follows_from(y,x) <-> causes(x,y)).",

"Assumption: What follows from something is determined by it to produce an effect":
"all x all y (follows_from(y,x) <-> determines_to_produce_effect(x,y)).",

"Assumption: What follows from something is determined by it to exist":
"all x all y (follows_from(y,x) <-> determines_to_exist(x,y)).",

"""Assumption: X determines y to produce an effect iff there is something z
such that x determines y to produce z""":
"all x all y (determines_to_produce_effect(x,y) <-> exists z (x_determines_y_to_produce_z(x,y,z))).",

"Assumption: What is finite has a determinate existence":
"all x (finite(x) <-> has_determinate_existence(x)).",

"Assumption: A substance is conceived through itself":
"all s ( is_substance(s) -> is_conceived_through(s,s) ).",

"Assumption: A substance exists in itself":
"all s ( is_substance(x) -> exists_in(s,s) ).",

"Assumption: God is a substance":
"all s ( is_god(s) -> is_substance(s) ).",

"Assumption: If it pertains to the nature of something to exist, then its essence involves existence":
"all s ( pertains_to_its_nature_to_exist(s) -> essence_involves_existence(s) ).",

"""Assumption: If something conceivably does not exist then its essence does not involve existence""":
"all s ( conceivably_does_not_exist(s) -> -essence_involves_existence(s) ).",

"Assumption: If something conceivably does not exist then it conceivably lacks existence":
"all s ( conceivably_does_not_exist(s) <-> ( all e ( is_existence(e) -> conceivably_lacks(s,e) ) ) ).",

"Assumption: What something conceivably lacks it possibly lacks":
"all x all F ( conceivably_lacks(x, F) <-> possibly_lacks(x, F) ).",

"Assumption: What something possibly lacks it does not necessarily have":
"all x all F ( possibly_lacks(x, F) <-> -necessarily_has(x, F) ).",

"Assumption: If something necessarily exists then it necessarily has existence":
"all x ( necessarily_exists(x) <-> ( all e ( is_existence(e) -> necessarily_has(x, e) ) ) ).",

"Assumption: If something is god it necessarily exists":
"all s ( is_god(s) -> necessarily_exists(s) )."
}


