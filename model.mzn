% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal1: assign groups of participants to courses
% satisfy all MUSTs, minimize NOs
% Goal2: assign courses to lecture halls and days
% such that advanced courses follow intro courses

enum SCORES = {M, O, N}; % MUST, OK, NO
int: MAX_HALLS = 5;
int: DAYS = 6;

enum people;
enum courses;
enum CourseOrEmpty = C(courses) ++ { Empty };
array[people, courses] of SCORES: marks;
array[courses] of int: lengths;

array[people] of var set of courses: people2courses;

enum halls = anon_enum(MAX_HALLS);
enum days = anon_enum(DAYS);

array[days, halls] of var CourseOrEmpty: schedule;
array[1..MAX_HALLS*DAYS] of var CourseOrEmpty: schedule_flat = [schedule[d, h] | d in days, h in halls];
array[days] of var set of courses: day2courses = [{C^-1(schedule[d, h]) | h in halls where schedule[d, h] != Empty} | d in days];
array[courses] of var set of halls: course2halls = [{h | d in days, h in halls where schedule[d, h] = C(c)} | c in courses];

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
    sum([lengths[c] | c in people2courses[p]]) = DAYS
);

% each course has less than 20 and more than 5 participants

constraint forall(c in courses) (
    5 <= sum([1 | p in people where c in people2courses[p]]) /\ sum([1 | p in people where c in people2courses[p]]) <= 20
);

% courses fill number of slots according to their lengths

constraint forall(c in courses) (
    count(schedule_flat, C(c)) = lengths[c]
);

% if a course is assigned to a hall, it stays in that hall

constraint forall(c in courses) (
    card(course2halls[c]) = 1
);

% advanced courses follow intro courses
% no slots of courses[4] are before slots of courses[3]
% no slots of courses[6] are before slots of courses[5]
% (other courses are not ordered)

constraint forall (d1 in days, d2 in days) (
    let { var set of courses: c1 = day2courses[d1];
          var set of courses: c2 = day2courses[d2]; }
    in
        (courses[4] in c2 /\ courses[3] in c1 -> d1 < d2) /\
        (courses[6] in c2 /\ courses[5] in c1 -> d1 < d2)
);

%

solve minimize negscore;

output ["assignment: \(people2courses[i]) | (\(people2musts[i]))\n" | i in index_set(people2courses)] ++
       ["\(c): \(sum([1 | p in people where c in people2courses[p]]))\n" | c in courses] ++
       % print schedule one day per line
       ["\(d): \([schedule[d, h] | h in halls])\n" | d in days] ++
       ["negscore: \(negscore)"];