% ------------------------------------------------------------------
% Hydroxyl 
% ------------------------------------------------------------------
% POSITIVES — contain an -OH (oxygen, single-bonded, exactly one H)
methanol((n/a, c, [h, h, h, (1, o, [h])])).
ethanol((n/a, c, [h, h, h, (1, c, [h, h, (1, o, [h])])])).
propan_1_ol((n/a, c, [h, h, h, (1, c, [h, h, (1, c, [h, h, (1, o, [h])])])])).

% NEGATIVES — no -OH
methane((n/a, c, [h, h, h, h])).
ethane((n/a, c, [h, h, h, (1, c, [h, h, h])])).
dimethyl_ether((n/a, c, [h, h, h, (1, o, [(1, c, [h, h, h])])])).  % has O, but O–C not O–H
formaldehyde((n/a, c, [h, h, (2, o, [])])).                       % has O, but C=O not O–H
methanethiol((n/a, c, [h, h, h, (1, s, [h])])).      %  -SH

% ------------------------------------------------------------------
%  Phenolic
% ------------------------------------------------------------------
% Positives
phenol(ring(n/a, [(a,c,[(1,o,[h])]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h])])).
p_cresol(ring(n/a, [(a,c,[(1,o,[h])]), (a,c,[h]), (a,c,[h]), (a,c,[(1,c,[h,h,h])]), (a,c,[h]), (a,c,[h])])).
chlorophenol(ring(n/a, [(a,c,[(1,o,[h])]), (a,c,[h]), (a,c,[h]), (a,c,[(1,cl,[])]), (a,c,[h]), (a,c,[h])])).

%Negatives
% (A) benzene, no OH
benzene(ring(n/a, [(a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h])]) ).
toluene(ring(n/a, [(a,c,[(1,c,[h,h,h])]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h])]) ).
% (B) OH, no benzene
ethanol((n/a, c, [h, h, h, (1, c, [h, h, (1, o, [h])])]) ).
cyclopentanol(ring(n/a, [(1,c,[h,(1,o,[h])]), (1,c,[h,h]), (1,c,[h,h]), (1,c,[h,h]), (1,c,[h,h])]) ).
% (C) benzene + oxygen limb that does NOT end in H  (anisole, -O-CH3)
anisole(ring(n/a, [(a,c,[(1,o,[(1,c,[h,h,h])])]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h]), (a,c,[h])]) ).