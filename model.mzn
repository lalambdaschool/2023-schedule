% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal: schedule courses to halls and days
% Subgoal1: if a person MUSTed a course, they must be able to attend it
% Subgoal2: minimize the number of people who NOed a course and can't not attend it
% Subgoal3: advanced courses must follow intro courses

enum SCORES = {M, O, N}; % MUST, OK, NO
int: MAX_HALLS = 5;
int: DAYS = 6;

enum people;
enum courses;
enum CourseOrEmpty = C(courses) ++ { Empty };
array[people, courses] of SCORES: marks;
array[courses] of int: lengths;

enum halls = anon_enum(MAX_HALLS);
enum days = anon_enum(DAYS);

array[days, halls] of var CourseOrEmpty: schedule;
% array[1..MAX_HALLS*DAYS] of var CourseOrEmpty: schedule_flat = [schedule[d, h] | d in days, h in halls];
array[days] of var set of courses: day2courses = [{C^-1(schedule[d, h]) | h in halls where schedule[d, h] != Empty} | d in days];
array[courses] of var set of halls: course2halls = [{h | d in days, h in halls where schedule[d, h] = C(c)} | c in courses];

% get course start date
% i.e. the first day of the course
array[courses] of var days: course2start = [min({d | d in days where c in day2courses[d]})| c in courses];

% invert this to map start date -> courses
array[days] of var set of courses: start2courses = [{c | c in courses where course2start[c] = d} | d in days];

% build a DAG of courses
% store as arrays of edges
% c1->c2 if c2 can be attended directly after c1
% that is, for dates d and d+1:
%  - c1 is scheduled on d and not d+1 (a participant must attend course to completion)
%  - c2 starts on d+1

array[courses, courses] of var bool: trajectories;

constraint forall (d1 in days) (
    is_fixed(enum_next(days, d1)) ->
    let { days: d2 = enum_next(days, d1);
          var set of courses: c1 = day2courses[d1];
          var set of courses: c2 = day2courses[d2]; }
    in
        forall(c in c1) (
            forall(c_ in c2 where not (c in c2)) (
                trajectories[c, c_] = true
            )
        )
);


% all available educational trajectories
% a trajectory is the set of courses one can take in sequence
% for instance, if a course takes 6 days, a trajectory will only contain this one course
% if a course takes 3 days, a trajectory will contain this course and another similar one

% array[1..card(courses)^2] of var set of courses: trajectories;

% follows relationship
% course c2 follows c1 if it can be attended after c1

array[courses] of var set of courses: follows;

% build follows from schedule
% take days d and d+1
% and corresponding course sets C1 and C2
% for each course c in C1:
%  if c in C2, skip (a participant must attend course to completion)
%  else, add C2 to trajectories[c]

constraint forall (d1 in days) (
    is_fixed(enum_next(days, d1)) ->
    let { days: d2 = enum_next(days, d1);
          var set of courses: c1 = day2courses[d1];
          var set of courses: c2 = day2courses[d2]; }
    in
        forall(c in c1 where not (c in c2)) (
            follows[c] = follows[c] union (c2 intersect start2courses[d2])
        )
);

% build trajectories
% a trajectory is a set containing:
% - course c1 starting on day 1
% - each c2 in follows[c1] makes a new trajectory
% - similarly each c_n+1 in follows[c_n] makes a new trajectory
% that is, the trajectories branch out: each new course in follows makes a new trajectory






% a person MUSTed a course
% they must be assigned to this course

array[people] of set of courses: people2musts = [{c | c in courses where marks[p, c] = M}| p in people];

% constraint forall(p in people) (
%     card(people2musts[p]) > 0 -> card(people2courses[p] ∩ people2musts[p]) > 0
% );

% a person NOed a course
% minimize such assignments

array[people] of set of courses: people2nos = [{c | c in courses where marks[p, c] = N}| p in people];

% var int: negscore;
% constraint negscore = sum([card(people2courses[p] ∩ people2nos[p]) | p in people]);

% a person OKed a course

array[people] of set of courses: people2oks = [{c | c in courses where marks[p, c] = O}| p in people];

% length of courses a person attends sums to 6 days

% constraint forall(p in people) (
%     sum([lengths[c] | c in people2courses[p]]) = DAYS
% );

% each course has less than 20 and more than 5 participants

% constraint forall(c in courses) (
%     5 <= sum([1 | p in people where c in people2courses[p]]) /\ sum([1 | p in people where c in people2courses[p]]) <= 20
% );

% courses fill number of slots according to their lengths

constraint forall(c in courses)(
  sum(d in days)(bool2int(c in day2courses[d])) = lengths[c]
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

% solve minimize negscore;

% output ["assignment: \(people2courses[i]) | (\(people2musts[i]))\n" | i in index_set(people2courses)] ++
    %    ["\(c): \(sum([1 | p in people where c in people2courses[p]]))\n" | c in courses] ++
       % print schedule one day per line
output ["\(d): \([schedule[d, h] | h in halls])\n" | d in days] ++
    %    ["\(i) -> \(follows[i])\n" | i in index_set(follows)] ++
       ["\(trajectories)\n\n"] ++
       ["\(course2halls)\n\n"] ++
       ["\(day2courses)\n\n"];
    %    ["negscore: \(negscore)"];