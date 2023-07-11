% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal1: assign groups of participants to courses
% satisfy all MUSTs, minimize NOs

enum SCORES = {M, O, N}; % MUST, OK, NO

enum people;
enum courses;
array[people, courses] of SCORES: marks;
array[courses] of int: lengths;

array[people] of var set of courses: people2courses;

% a person MUSTed a course
% they must be assigned to this course

array[people] of set of courses: people2musts = [{c | c in courses where marks[p, c] = M}| p in people];

constraint forall(p in people) (
    card(people2musts[p]) > 0 -> card(people2courses[p] ∩ people2musts[p]) > 0
);

% a person NOed a course
% minimize such assignments

array[people] of set of courses: people2nos = [{c | c in courses where marks[p, c] = N}| p in people];

var int: negscore;
constraint negscore = sum([card(people2courses[p] ∩ people2nos[p]) | p in people]);

% a person OKed a course

array[people] of set of courses: people2oks = [{c | c in courses where marks[p, c] = O}| p in people];

% length of courses a person attends sums to 6 days

constraint forall(p in people) (
    sum([lengths[c] | c in people2courses[p]]) = 6
);

% each course has less than 20 and more than 5 participants

constraint forall(c in courses) (
    5 <= sum([1 | p in people where c in people2courses[p]]) /\ sum([1 | p in people where c in people2courses[p]]) <= 20
);

solve minimize negscore;

output ["assignment: \(people2courses[i]) | (\(people2musts[i]))\n" | i in index_set(people2courses)] ++
       ["\(c): \(sum([1 | p in people where c in people2courses[p]]))\n" | c in courses] ++
       ["negscore: \(negscore)"];