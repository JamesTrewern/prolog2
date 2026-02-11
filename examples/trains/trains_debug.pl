%% metarules
P(A):-Q(A),{P,Q}.
P(A):-Q(A),R(A),{P,Q,R}.
P(A):-Q(A,B),R(B),{P,Q,R}.

%% Minimal background knowledge
short(car_11).
short(car_12).
closed(car_12).
has_car(east1,car_11).
has_car(east1,car_12).
has_car(west6,car_61).
has_car(west6,car_62).
closed(car_61).
short(car_62).
