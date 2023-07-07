% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal: assign groups of participants to courses
% satisfy all MUSTs and NOs, maximise OKs

enum SCORES = {M, O, N}; % MUST, OK, NO

enum people;
enum courses;

array[people, courses] of SCORES: marks;
array[people] of var set of courses: people2courses;

% a person MUSTed a course
% they must be assigned to this course

array[people] of set of courses: people2musts = [{c | c in courses where marks[p, c] = M}| p in people];

constraint forall(p in people) (
    card(people2musts[p]) > 0 -> card(people2courses[p] ∩ people2musts[p]) > 0
);

% a person NOed a course
% they must not be assigned to this course

array[people] of set of courses: people2nos = [{c | c in courses where marks[p, c] = N}| p in people];

constraint forall(p in people) (
    not (card(people2courses[p] ∩ people2nos[p]) > 0)
);

% a person OKed a course
% and they are assigned to this course
% => score++

array[people] of set of courses: people2oks = [{c | c in courses where marks[p, c] = O}| p in people];

var int: score;
constraint score = sum([card(people2courses[p] ∩ people2oks[p]) | p in people]);

solve maximize score;

output ["p2c: ", show(people2courses), "\n",
        "p2m: ", show(people2musts), "\n",
        "p2n: ", show(people2nos), "\n",
        "score: ", show(score)];