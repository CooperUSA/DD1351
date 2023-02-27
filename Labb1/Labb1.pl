%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 1	(4p)
% unifiering
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
%    ?- T=f(a,Y,Z), T=f(X,X,b)
%  Den ger:
%    T = f(a, a, b),
%    Y = X, X = a,
%    Z = b
Då X är ej bundet, så binds först X till "a",    => X=a 
sen jämförs Y och (X=a), då X är bundet till "a" så binds Y till X (vilket är bundet till "a"), => Y=X, X=a
sen då Z är ej bundet, så binds Z till "b".   => Z=b
T=f(X,Y,Z) => T=f(a, a, b)
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 2 	(6p)
% representation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% remove_duplicates([1,2,3,2,4,1,3,4], E).

remove_duplicates([],[]).
remove_duplicates([Head|Tail], [Head|Result]) :- 
    member(Head, Tail),
    min_delete(Head, Tail, NewResult), 
    remove_duplicates(NewResult,Result).

remove_duplicates([Head|Tail],[Head|Result]):-
    remove_duplicates(Tail, Result).

min_delete(_,[],[]).
min_delete(X,[X|Tail], Result):- min_delete(X, Tail, Result).
min_delete(X,[Head|Tail],[Head|Result]) :- min_delete(X, Tail, Result).

/*
Första gången så är Head=1, "member(Head,Tail)" kommer se att det finns fler ettor i listan och kommer då gå till delete.
Vid "min_delete(Head, Tail, NewResult)" så är Head=1 och Tail (som är resten av listan) inputs, och ger output Result.

"min_delete" sparar Head för att jämföra med varje index i tail, mm det inte är en duplicate så kopierar den över elementet till Result.
Efter den har kollat hela Tail så kommer Result vara identisk till Tail, förutom att den har tagit bort alla element som är likadana som Head
Ex. Head=1  Tail=[2,3,2,4,1,3,4]  =>  Result=[2,3,2,4,3,4] 

"remove_duplicate" kollar om Head har några duplicates i listan, om den inte har det så rör sig head fram ett stig i listan och därmed kollar
nästa tal. Om det finns duplikata tal så kallas "min_delete", varav delete ger sedan tillbaka en lista utan duplikata elementen.
*/

mdaga@kth.se
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 3	(6p)
% rekursion och backtracking  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% append([],L,L).
% append([H|T],L,[H|R]) :- append(T,L,R).

partstring(List, L, F) :- 
    append(_, Temp, List), 
    append(F, _, Temp), 
    length(F, L), 
    L>0.

/*
När partstring är kallat så kommer den kalla första append, varav den anonyma variablen "_" tar värdet av en tomm lista och "Temp" tar
värdet av List. Sen exitar den anropet av första append.
I andra append så tar värdet "F" värdet av en tomm lista och "_" tar då värdet av "Temp"(=List). Därav är F=[]. Men då längden av listan
F är noll, så misslyckas koden.

Den andra append gör en redo och där får "F" första elementet av "List", vilket i sin tur gör att den anonyma variabeln "_" tar värdet av
resten av "List" (vid rekursivitet) för att append ska kunna stämma.

Detta fortsätter rekursivt, tills "F" har blivit hela listan "List". Då misslyckas koden och återkallas från första append, vilket
gör att "Temp" tar värde av listan "List" men utan dens första element. 
Sedan börjar loopen om igen. 
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 4       (8p)
% representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%anta att vi har noderna
node(1,3).
node(1,5).
node(1,7).
node(2,3).
node(3,5).
node(4,6).
node(5,4).
node(7,6).
node(1,6).

%vi kollar om X är relaterat till Y på något sätt, sådant att noderna inte måste vara så många
nodesConnected(X,Y):- node(X,Y); node(Y,X).

%för att hitta en väg från a till f måste
%1. a måste ha vägar som nodesConnected returnerar true för att gå vidare
%2. om a har en nod som är relaterad till andra noder ska den nya noden finna f på sin noder igen

%Vi vill röra oss mellan noderna då vi hittar en nod som är relaterat till X
hitta(A, B, P) :- 
    ga(A, B, [A], Vag), 
    reverse(Vag, P). %kopierar Vag till P

%basfall
ga(A, B, Vag, [B|Vag]) :- nodesConnected(A, B).

%rekurisvafallet, eftersom vi inte vill gå runt i cirklar ibland så måste vi komma ihåg vilka vägar vi redan har tagit.
%därav finns "Besökta" listan som kommer ihåg dessa väggar och jämförs vid respektive tillfälle det möjligen vägar som kan tas. 
%Men då dess läggs till hamnar dom i omvänd ordning. Vi vet dock hur vi definerar ett predikat som byter ordning  
ga(A, B, Besokta, P) :- 
    nodesConnected(A, C),
    C \== B,
    \+member(C,Besokta),
    ga(C, B, [C|Besokta], P).

reverse([],[]).
reverse([H|T], R) :- reverse(T,S), append(S, [H], R).









%Basfall
% partstring([X|_], 1, [X]). 

% partstring([H|T], L, F):- partstring([H|T], L1, Result), helper(T, Result, F), L is L1+1.
% helper([H|T], Result, F):- append(Result, [H], F).