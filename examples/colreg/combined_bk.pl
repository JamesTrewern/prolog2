





%  GEOMETRIC ABSTRACTION
port_forward(X,Y)      :- sector(X,Y,port_bow_forward).
port_forward(X,Y)      :- sector(X,Y,port_bow_broad).
port_forward(X,Y)      :- sector(X,Y,port_beam_forward).
port_aft(X,Y)          :- sector(X,Y,port_beam_aft).
port_aft(X,Y)          :- sector(X,Y,port_quarter_broad).
port_aft(X,Y)          :- sector(X,Y,port_quarter_aft).
starboard_forward(X,Y) :- sector(X,Y,starboard_bow_forward).
starboard_forward(X,Y) :- sector(X,Y,starboard_bow_broad).
starboard_forward(X,Y) :- sector(X,Y,starboard_beam_forward).
starboard_aft(X,Y)     :- sector(X,Y,starboard_beam_aft).
starboard_aft(X,Y)     :- sector(X,Y,starboard_quarter_broad).
starboard_aft(X,Y)     :- sector(X,Y,starboard_quarter_aft).

port(X,Y)      :- port_forward(X,Y).
port(X,Y)      :- port_aft(X,Y).
port(X,Y)      :- sector(X,Y,port_beam).
starboard(X,Y) :- starboard_forward(X,Y).
starboard(X,Y) :- starboard_aft(X,Y).
starboard(X,Y) :- sector(X,Y,starboard_beam).
forward(X,Y)   :- port_forward(X,Y).
forward(X,Y)   :- starboard_forward(X,Y).
forward(X,Y)   :- sector(X,Y,ahead).
aft(X,Y)       :- port_aft(X,Y).
aft(X,Y)       :- starboard_aft(X,Y).
aft(X,Y)       :- sector(X,Y,astern).


% ORDERINGS

% range
less_and_adjacent(far,very_far).
less_and_adjacent(middle,far).
less_and_adjacent(near,middle).
less_and_adjacent(very_near,near).

% tcpa
less_and_adjacent(long,very_long).
less_and_adjacent(medium,long).
less_and_adjacent(short,medium).
less_and_adjacent(immediate,short).

% dcpa
less_and_adjacent(marginal,safe).
less_and_adjacent(close,marginal).
less_and_adjacent(very_close,close).
less_and_adjacent(critical,very_close).

% turn magnitude
less_and_adjacent(large,very_large).
less_and_adjacent(moderate,large).
less_and_adjacent(small,moderate).
less_and_adjacent(insubstantial,small).

% Avoid Resume Risks
less_and_adjacent(no_risk, risk_developing).
less_and_adjacent(risk_developing, medium_close).
less_and_adjacent(medium_close, medium_veryclose).
less_and_adjacent(medium_veryclose, medium_close).
less_and_adjacent(medium_critical, short_close).
less_and_adjacent(short_close, short_veryclose).
less_and_adjacent(short_veryclose, short_critical).
less_and_adjacent(short_critical, imminent_close).
less_and_adjacent(imminent_close, imminent_veryclose).
less_and_adjacent(imminent_veryclose, imminent_critical).

less_than(X,Y) :- 
    less_and_adjacent(X,Z), 
    less_than(Z,Y).
less_than(X,Y) :-
    less_and_adjacent(X,Y).

greater_than(X,Y) :- 
    less_and_adjacent(Z,X), 
    greater_than(Z,Y).
greater_than(X,Y) :-
    less_and_adjacent(Y,X).

less_or_equal(X,Y) :- X = Y.
less_or_equal(X,Y) :- less_than(X,Y).

greater_or_equal(X,Y) :- X = Y.
greater_or_equal(X,Y) :- greater_than(X,Y).

range_gt(X,Y,A):-
    range(X,Y,B),
    greater_than(B,A).
range_ge(X,Y,A):-
    range(X,Y,B),
    greater_or_equal(B,A).
range_lt(X,Y,A):-
    range(X,Y,B),
    less_than(B,A).
range_le(X,Y,A):-
    range(X,Y,B),
    less_or_equal(B,A).


dcpa_gt(X,Y,A):-
    dcpa(X,Y,B),
    greater_than(B,A).
dcpa_ge(X,Y,A):-
    dcpa(X,Y,B),
    greater_or_equal(B,A).
dcpa_lt(X,Y,A):-
    dcpa(X,Y,B),
    less_than(B,A).
dcpa_le(X,Y,A):-
    dcpa(X,Y,B),
    less_or_equal(B,A).

tcpa_gt(X,Y,A):-
    tcpa(X,Y,B),
    greater_than(B,A).
tcpa_ge(X,Y,A):-
    tcpa(X,Y,B),
    greater_or_equal(B,A).
tcpa_lt(X,Y,A):-
    tcpa(X,Y,B),
    less_than(B,A).
tcpa_le(X,Y,A):-
    tcpa(X,Y,B),
    less_or_equal(B,A).

is_range(Range) :- member(Range,[very_far,far,middle,near,very_near]).
is_dcpa(DCPA) :- member(DCPA,[safe,marginal,close,very_close,critical]). 
is_tcpa(TCPA) :- member(TCPA,[very_long,long,medium,short,immediate]).
is_turn(Turn) :- member(Turn, [very_large, large, moderate, small, insubstantial]).



%  CONCEPTUAL GROUPINGS

dcpa_acceptable(X,Y) :- dcpa(X,Y,marginal).
dcpa_acceptable(X,Y) :- dcpa(X,Y,safe).
dcpa_unacceptable(X,Y) :- not(dcpa_acceptable(X,Y)).

tcpa_closing(X,Y) :- not(tcpa(X,Y,opening)).

actionable_range(X,Y) :- not(range(X,Y,very_far)).


%  ample_time  (Rule 8(a))

ample_time(X,Y)    :- tcpa(X,Y,medium).
ample_time(X,Y)    :- tcpa(X,Y,long).
ample_time(X,Y)    :- tcpa(X,Y,very_long).



%  RISK OF COLLISION (Rule 7)

collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,imminent).
collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,short).
collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,medium).


%  CLOSE-QUARTERS SITUATION (Rule 8)

close_quarters_developing(X,Y) :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,far).
close_quarters_developing(X,Y) :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,middle).
close_quarters(X,Y)            :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,near).
close_quarters(X,Y)            :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,very_near).


%  ENCOUNTER  (three types, one per pair) - the finding of fact

encounter(X,Y,rule13_overtaking) :-
    collision_risk(X,Y),
    arc_overtaking(X,Y).

encounter(X,Y,rule14_head_on) :-
    collision_risk(X,Y),
    mutual_ahead(X,Y),
    not(arc_overtaking(X,Y)),
    not(arc_overtaking(Y,X)).

encounter(X,Y,rule15_crossing) :-
    collision_risk(X,Y),
    not(arc_overtaking(X,Y)),
    not(arc_overtaking(Y,X)),
    not(mutual_ahead(X,Y)).

mutual_ahead(X,Y):-
    sector(X,Y,ahead),
    sector(Y,X,ahead).
%  ENCOUNTER + DUTY  (Own, Target, Encounter, Duty) - the conclusion of law

encounter_and_duty(X,Y,rule13_overtaking,rule16_giveway) :- encounter(X,Y,rule13_overtaking).   % X overtakes Y
encounter_and_duty(X,Y,rule13_overtaking,rule17_standon) :- encounter(Y,X,rule13_overtaking).   % Y overtakes X
encounter_and_duty(X,Y,rule14_head_on,rule16_giveway)    :- encounter(X,Y,rule14_head_on).        % head-on: mutual
encounter_and_duty(X,Y,rule15_crossing,rule16_giveway)   :- encounter(X,Y,rule15_crossing), starboard(X,Y).
encounter_and_duty(X,Y,rule15_crossing,rule17_standon)   :- encounter(X,Y,rule15_crossing), port(X,Y).
encounter_and_duty(X,Y,rule15_crossing,rule16_giveway)   :- encounter(X,Y,rule15_crossing), port(Y,X).
encounter_and_duty(X,Y,rule15_crossing,rule17_standon)   :- encounter(X,Y,rule15_crossing), starboard(Y,X).


%  CONDUCT  (action form of the duty) - only stand-on is sub-classified, by ample_time

conduct(X,Y,rule17_standon_maintain) :- encounter_and_duty(X,Y,_,rule17_standon), ample_time(X,Y).
conduct(X,Y,rule17_standon_may_act)  :- encounter_and_duty(X,Y,_,rule17_standon), tcpa(X,Y,short).
conduct(X,Y,rule17_standon_must_act) :- encounter_and_duty(X,Y,_,rule17_standon), tcpa(X,Y,imminent).


%  EMERGENCY  - in extremis, departure from any rule; encounter-agnostic (Rule 2(b))

rule2_extremis(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,imminent).
%might be a cleaner way to do this
sector(agent0,cruiseliner1_0,starboard_bow_forward).
range(agent0,cruiseliner1_0,very_far).
dcpa(agent0,cruiseliner1_0,critical).
tcpa(agent0,cruiseliner1_0,long).
sector(cruiseliner1_0,agent0,port_bow_broad).
range(cruiseliner1_0,agent0,very_far).
dcpa(cruiseliner1_0,agent0,critical).
tcpa(cruiseliner1_0,agent0,long).
sector(agent1,cruiseliner1_1,starboard_bow_forward).
range(agent1,cruiseliner1_1,middle).
dcpa(agent1,cruiseliner1_1,critical).
tcpa(agent1,cruiseliner1_1,short).
sector(cruiseliner1_1,agent1,port_bow_broad).
range(cruiseliner1_1,agent1,middle).
dcpa(cruiseliner1_1,agent1,critical).
tcpa(cruiseliner1_1,agent1,short).
sector(agent2,cruiseliner1_2,starboard_bow_forward).
range(agent2,cruiseliner1_2,far).
dcpa(agent2,cruiseliner1_2,critical).
tcpa(agent2,cruiseliner1_2,medium).
sector(cruiseliner1_2,agent2,port_bow_broad).
range(cruiseliner1_2,agent2,far).
dcpa(cruiseliner1_2,agent2,critical).
tcpa(cruiseliner1_2,agent2,medium).
sector(agent3,cruiseliner1_3,port_bow_broad).
range(agent3,cruiseliner1_3,very_far).
dcpa(agent3,cruiseliner1_3,critical).
tcpa(agent3,cruiseliner1_3,long).
sector(cruiseliner1_3,agent3,starboard_bow_broad).
range(cruiseliner1_3,agent3,very_far).
dcpa(cruiseliner1_3,agent3,critical).
tcpa(cruiseliner1_3,agent3,long).
sector(agent4,cruiseliner1_4,port_bow_broad).
range(agent4,cruiseliner1_4,far).
dcpa(agent4,cruiseliner1_4,critical).
tcpa(agent4,cruiseliner1_4,medium).
sector(cruiseliner1_4,agent4,starboard_bow_broad).
range(cruiseliner1_4,agent4,far).
dcpa(cruiseliner1_4,agent4,critical).
tcpa(cruiseliner1_4,agent4,medium).
sector(agent5,cruiseliner1_5,port_bow_broad).
range(agent5,cruiseliner1_5,middle).
dcpa(agent5,cruiseliner1_5,critical).
tcpa(agent5,cruiseliner1_5,short).
sector(cruiseliner1_5,agent5,starboard_bow_broad).
range(cruiseliner1_5,agent5,middle).
dcpa(cruiseliner1_5,agent5,critical).
tcpa(cruiseliner1_5,agent5,short).
sector(agent6,cruiseliner1_6,port_bow_broad).
range(agent6,cruiseliner1_6,very_near).
dcpa(agent6,cruiseliner1_6,critical).
tcpa(agent6,cruiseliner1_6,imminent).
sector(cruiseliner1_6,agent6,starboard_bow_broad).
range(cruiseliner1_6,agent6,very_near).
dcpa(cruiseliner1_6,agent6,critical).
tcpa(cruiseliner1_6,agent6,imminent).
sector(agent7,cruiseliner1_7,ahead).
range(agent7,cruiseliner1_7,very_far).
sector(cruiseliner1_7,agent7,ahead).
range(cruiseliner1_7,agent7,very_far).
waypoint_reached(cruiseliner1_7).
sector(agent8,cruiseliner1_8,ahead).
range(agent8,cruiseliner1_8,very_far).
dcpa(agent8,cruiseliner1_8,critical).
tcpa(agent8,cruiseliner1_8,medium).
sector(cruiseliner1_8,agent8,ahead).
range(cruiseliner1_8,agent8,very_far).
dcpa(cruiseliner1_8,agent8,critical).
tcpa(cruiseliner1_8,agent8,medium).
sector(agent9,cruiseliner1_9,ahead).
range(agent9,cruiseliner1_9,middle).
dcpa(agent9,cruiseliner1_9,critical).
tcpa(agent9,cruiseliner1_9,short).
sector(cruiseliner1_9,agent9,ahead).
range(cruiseliner1_9,agent9,middle).
dcpa(cruiseliner1_9,agent9,critical).
tcpa(cruiseliner1_9,agent9,short).
sector(agent10,cruiseliner1_10,ahead).
range(agent10,cruiseliner1_10,middle).
dcpa(agent10,cruiseliner1_10,critical).
tcpa(agent10,cruiseliner1_10,long).
sector(cruiseliner1_10,agent10,astern).
arc_overtaking(agent10,cruiseliner1_10).
range(cruiseliner1_10,agent10,middle).
dcpa(cruiseliner1_10,agent10,critical).
tcpa(cruiseliner1_10,agent10,long).
sector(agent11,cruiseliner1_11,ahead).
range(agent11,cruiseliner1_11,near).
dcpa(agent11,cruiseliner1_11,critical).
tcpa(agent11,cruiseliner1_11,medium).
sector(cruiseliner1_11,agent11,astern).
arc_overtaking(agent11,cruiseliner1_11).
range(cruiseliner1_11,agent11,near).
dcpa(cruiseliner1_11,agent11,critical).
tcpa(cruiseliner1_11,agent11,medium).
sector(agent12,cruiseliner1_12,ahead).
range(agent12,cruiseliner1_12,very_near).
dcpa(agent12,cruiseliner1_12,critical).
tcpa(agent12,cruiseliner1_12,short).
sector(cruiseliner1_12,agent12,astern).
arc_overtaking(agent12,cruiseliner1_12).
range(cruiseliner1_12,agent12,very_near).
dcpa(cruiseliner1_12,agent12,critical).
tcpa(cruiseliner1_12,agent12,short).
sector(agent13,vessel_13,starboard_beam_forward).
range(agent13,vessel_13,far).
dcpa(agent13,vessel_13,safe).
tcpa(agent13,vessel_13,short).
sector(vessel_13,agent13,starboard_bow_broad).
range(vessel_13,agent13,far).
dcpa(vessel_13,agent13,safe).
tcpa(vessel_13,agent13,short).
