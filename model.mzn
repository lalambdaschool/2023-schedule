% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal: assign groups of participants to courses
% satisfy all MUSTs and NOs, maximise OKs

enum SCORES = {M, O, N}; % MUST, OK, NO

enum people;
enum courses;

array[people, courses] of SCORES: marks;
array[people] of var courses: people2courses; % FIXME: should be of var set courses

% a person MUSTed a course
% they must be assigned to this course

array[people] of set of courses: people2musts = [{c | c in courses where marks[p, c] = M}| p in people];

constraint forall(p in people) (
    card(people2musts[p]) > 0 -> people2courses[p] in people2musts[p]
);

% a person NOed a course
% they must not be assigned to this course

array[people] of set of courses: people2nos = [{c | c in courses where marks[p, c] = N}| p in people];

constraint forall(p in people) (
    not (people2courses[p] in people2nos[p])
);

% a person OKed a course
% and they are assigned to this course
% => score++

array[people] of set of courses: people2oks = [{c | c in courses where marks[p, c] = O}| p in people];

var int: score;
constraint score = sum([people2courses[p] in people2oks[p] | p in people]);

solve maximize score;

output ["p2c: ", show(people2courses), "\n",
        "p2m: ", show(people2musts), "\n",
        "p2n: ", show(people2nos), "\n",
        "score: ", show(score)];