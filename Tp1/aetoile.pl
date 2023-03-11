%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 
	
	% lancement de Aetoile
	initial_state(S0),
	G0 is 0,
	heuristique(S0,H0),
	F0 is H0+G0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pf1),
	insert([S0,[F0,H0,G0],nil,nil],Pu,Pu1),
	aetoile(Pf1,Pu1,Q).



%*******************************************************************************

aetoile([],[],_) :-
	print('PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !\n' ).
aetoile(Pf, Pu, Q) :-
	suppress_min([V,U],Pf,_),
	(final_state(U) ->
		belongs([U,V,Pere,A],Pu), 
		insert([U,V,Pere,A],Q,Qf),
		affiche_solution(Qf,[U,V,Pere,A])
	;	
		% Suppresion de pf et pu 
		suppress_min([[Ff,Hf,Gf],Uf],Pf,Pfint),
		belongs([Uf,[Ff,Hf,Gf],Pere,Action],Pu),
		suppress([Uf,[Ff,Hf,Gf],Pere,Action],Pu,Puint),
		%Développer U
		expand([[_,_,Gf],Uf],Successors),
		loop_successors(Successors,Pfint,Puint,Q,Pfnew,Punew),
		insert([Uf,[Ff,Hf,Gf],Pere,Action],Q,Qnew),
		aetoile(Pfnew,Punew,Qnew)
	).


affiche_solution(Q,[Actuel,V,Pere,A]):-
	suppress([Actuel,V,Pere,A],Q,Qp),
	(
		belongs([Pere,Vp,Perep,Ap],Qp) -> 
		affiche_solution(Qp,[Pere, Vp, Perep, Ap]),
		writeln(A),
		writeln(Actuel)
	;
		writeln('Debut:')
	).
	
	
%Av = action, V = état arrivée, Kuv= coût et on calcule Fv,Hv,Gv
expand([[_,_,G],U],Successors) :-
	findall([V,[Fv,Hv,Gv],U,Av], (rule(Av,Kuv,U,V),heuristique(V,Hv),Gv is G+Kuv,Fv is Gv+Hv), Successors).

treat_1successor([V,[Fv,Hv,Gv],U,Av],Pf,Pu,Q,Pfaux,Puaux) :-
	((belongs([V,_,_,_],Q)) -> 
	Pfaux = Pf, Puaux= Pu
	;
		((suppress([V,[Fold,Hold,Gold],Uold,Aold],Pu,Puint)) ->
			(([Fv,Hv,Gv] @< [Fold,Hold,Gold]) -> 
			suppress([[Fold,Hold,Gold],V],Pf,Pfint),
			insert([V,[Fv,Hv,Gv],U,Av],Puint,Puaux),
			insert([[Fv,Hv,Gv],V],Pfint,Pfaux)
			;
			Pfaux=Pf, 
			insert([V,[Fold,Hold,Gold],Uold,Aold],Puint,Puaux)
			)
		;
		insert([V,[Fv,Hv,Gv],U,Av],Pu,Puaux),
		insert([[Fv,Hv,Gv],V],Pf,Pfaux)
		)
	).

loop_successors([],Pf,Pu,_,Pf,Pu).
loop_successors([First|Rest], Pf,Pu,Q,Pfnew,Punew) :-
	treat_1successor(First,Pf,Pu,Q,Pfaux,Puaux),
	loop_successors(Rest,Pfaux,Puaux,Q,Pfnew,Punew).

%test unitaires à faire
test_uni :-
	initial_state(S0),
	G0 is 0,
	heuristique(S0,H0),
	F0 is H0+G0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pf1),
	insert([S0,[F0,H0,G0],nil,nil],Pu,Pu1),
	expand([[F0,H0,G0],S0],Successors),
	loop_successors(Successors, Pf1,Pu1,Q,Pfnew,Punew),
	writeln('Pfnew'),
	put_flat(Pfnew),
	writeln('\nPunew'),
	put_flat(Punew).