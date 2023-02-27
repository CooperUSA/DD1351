verify(InputFileName):-   
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof, Proof).

%Needs an ackumalator to move back 
valid_proof(Prems, Goal, [X|[]], Ackum):-
    (prem(X, Prems) ; copy(X, Ackum) ; andintro(X, Ackum) ; andeli1(X, Ackum) ; andeli2(X, Ackum) ; 
    orintro1(X, Ackum) ; orintro2(X, Ackum) ; orelim(X, Ackum) ; impintro(X, Ackum) ; impelim(X, Ackum) ;  
    negintro(X, Ackum) ; negelim(X, Ackum) ; contelim(X, Ackum) ; negnegintro(X, Ackum) ; negnegelim(X, Ackum) ; 
    mt(X, Ackum) ; pbc(X, Ackum) ; lem(X) ; box(Prems, X, Ackum)), 
    X = [_, Goal, _].

valid_proof(Prems, Goal, [X|T], Ackum):-
    (prem(X, Prems) ; copy(X, Ackum) ; andintro(X, Ackum) ; andeli1(X, Ackum) ; andeli2(X, Ackum) ; 
    orintro1(X, Ackum) ; orintro2(X, Ackum) ; orelim(X, Ackum) ; impintro(X, Ackum) ; impelim(X, Ackum) ;  
    negintro(X, Ackum) ; negelim(X, Ackum) ; contelim(X, Ackum) ; negnegintro(X, Ackum) ; negnegelim(X, Ackum) ; 
    mt(X, Ackum) ; pbc(X, Ackum) ; lem(X) ; box(Prems, X, Ackum)), 
    valid_proof(Prems, Goal, T, Ackum).


%Premise
prem([_, X, premise], Prems):- 
    member(X, Prems).

%Copy
copy([Num, X, copy(Pos)], Ackum):-
    Num > Pos,
    member([Pos, X, _], Ackum).

%And introduction
andintro([Num, and(X, Y), andint(Pos1, Pos2)], Ackum):-
    Num > Pos1,
    Num > Pos2,
    member([Pos1, X, _], Ackum),
    member([Pos2, Y, _], Ackum).

%And elimination of left field
andeli1([Num, X, andel1(Pos)], Ackum):-
    Num > Pos,
    member([Pos, and(X, _), _], Ackum).

%And elimination of right field
andeli2([Num, Y, andel2(Pos)], Ackum):-
    Num > Pos,
    member([Pos, and(_, Y), _], Ackum).

%Or introduction with left field
orintro1([Num, or(X, _), orint1(Pos)], Ackum):-
    Num > Pos,
    member([Pos, X, _], Ackum).

%Or introduction with right field
orintro2([Num, or(_, Y), orint2(Pos)], Ackum):-
    Num > Pos,
    member([Pos, Y, _], Ackum).

%Or elimination
orelim([Num, _, orel(Pos1,Pos2,Pos3,Pos4,Pos5)], Ackum):-
    Num > Pos1, 
    Num > Pos2,
    Num > Pos3,
    Num > Pos4,
    Num > Pos5,
    member([Pos1, or(X, Y), _], Ackum),     %Gets the functions X and Z from the refferenced row.
    findbox(Ackum, Pos2, X, Pos3, Z),
    findbox(Ackum, Pos4, Y, Pos5, Z).

%Implication Introduction
impintro([Num, imp(X, Y), impint(Pos1, Pos2)], Ackum):-
    Num > Pos1,
    Num > Pos2,
    findbox(Ackum, Pos1, X, Pos2, Y).

%Implication elimination
impelim([Num, X, impel(Pos1, Pos2)], Ackum):- 
    Num > Pos1,   
    Num > Pos2,                     %Too check that it's not refering to a row further down.
    member([Pos1, Y, _ ], Ackum),
    member([Pos2, imp(Y,X), _], Ackum).

negintro([Num, neg(X), negint(Pos1, Pos2)], Ackum):-
    Num > Pos1, 
    Num > Pos2,
    findbox(Ackum, Pos1, X, Pos2, cont).

%Negation elimination
negelim([Num, cont, negel(Pos1, Pos2)], Ackum):-
    Num > Pos1,   
    Num > Pos2, 
    member([Pos1, X, _], Ackum),
    member([Pos2, neg(X), _], Ackum).

%Contradiction elimination
contelim([Num, _, contel(Pos)], Ackum):-
    Num > Pos,
    member([Pos, cont, _], Ackum).

%Double negation introduction
negnegintro([Num, neg(neg(X)), negnegint(Pos)], Ackum):-
    Num > Pos,
    member([Pos, X, _], Ackum).

%Double negation elimination
negnegelim([Num, X, negnegel(Pos)], Ackum):-
    Num > Pos,
    member([Pos, neg(neg(X)), _], Ackum).

mt([Num, neg(X), mt(Pos1, Pos2)], Ackum):-
    Num > Pos1,
    Num > Pos2,
    member([Pos1, imp(X, Y), _], Ackum),
    member([Pos2, neg(Y), _], Ackum).

pbc([Num, X, pbc(Pos1, Pos2)], Ackum):-
    Num > Pos1, 
    Num > Pos2,
    findbox(Ackum, Pos1, neg(X), Pos2, cont).

lem([_, or(X, neg(X)), lem]).



% %Box (recievess premisses since we have to check which premisses we have again)(Probably don't need it, since T shouldn't have any premisses)
% box([X|T], Ackum):- 
%     X = [_, _, assumption],                 %Johan said that we should expect that every box starts with an assumption. Also makes sure the a box that starts with an assumption
%     append([X|T], Ackum, Bevis),            %Since if it's a nestled box, we can't use member with Ackum. Since we would have sent to valid_proof a box in Ackum, so when we check, E.g impeli, it couldn't check for member with Ackum, since that row is a list within a box within Ackum.
%     valid_proof(_, _, T, Bevis).            %Now we send an ackumalator that also has the rows of the box we're inside and not just the box, which member can't check.

box(Prems, [X|T], Ackum):-                    %{Med Prems}
    X = [_, _, assumption],                 
    append([X|T], Ackum, Bevis),
    valid_proof(Prems, _, T, Bevis).

% Finds the box with the appropriate rows we're looking for, checks the first row in the box is correct. Also sees if the other row is somewhere in the box (which should be the last row as long as the rule referred to it correctly).
findbox([[[Pos1, X, assumption]|T1]|_], Pos1, X, Pos2, Y):-     %Find the box that starts on a specific row and is a assumption 
    member([Pos2, Y, _], T1).   %Only member in T1 and not [[Pos1, X, assumption]|T1], since a box should atleast have the size of 2 rows.     

findbox([_|T], Pos1, X, Pos2, Y):-
    findbox(T, Pos1, X, Pos2, Y).
