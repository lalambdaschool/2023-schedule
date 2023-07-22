% Input:
% {participant -> course} = {MUST, OK, NO}
% Goal: schedule courses to halls and days
% Subgoal1: if a person MUSTed a course, they must be able to attend it
% Subgoal2: minimize the number of people who NOed a course and can't not attend it
% Subgoal3: advanced courses must follow intro courses

include "globals.mzn";

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

array[people, days] of var CourseOrEmpty: schedule;

array[days] of var set of CourseOrEmpty: day2courses = [{schedule[p, d] | p in people} | d in days];
array[people] of var set of courses: people2courses = [{C^-1(schedule[p, d]) | d in days where schedule[p, d] != Empty} | p in people];

% get course start date
% i.e. the first day of the course
array[courses] of var days: course2start = [min({d | d in days where c in day2courses[d]})| c in courses];

% invert this to map start date -> courses
array[days] of var set of courses: start2courses = [{c | c in courses where course2start[c] = d} | d in days];

% no more than MAX_HALLS courses per day

constraint forall(d in days) (
    card(day2courses[d]) <= MAX_HALLS
);

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

% constraint forall(c in courses) (
%     5 <= sum([1 | p in people where c in people2courses[p]]) /\ sum([1 | p in people where c in people2courses[p]]) <= 20
% );

array[courses] of var 1..card(people): course2count = [sum([1 | p in people where c in people2courses[p]]) | c in courses];

% constraint forall (c in courses) (
%     course2count[c] > 5 /\ course2count[c] < 20
% );

% courses fill number of slots according to their lengths

constraint forall(c in courses)(
  sum(d in days)(bool2int(c in day2courses[d])) = lengths[c]
);

% courses always start on day DAYS-lengths[c] at the latest

% constraint forall(c in courses)(
%   course2start[c] >= DAYS-lengths[c]
% );

% courses are assigned without gaps
% \A c, day2courses[d] contains c where d in course2start[c]..course2start[c]+lengths[c]-1

constraint forall(c in courses) (
    % XXX
    forall(d in course2start[c]..(course2start[c]+lengths[c]-1) where d < DAYS) (
        c in day2courses[to_enum(days, d)]
    )
);


% if a course is assigned to a hall, it stays in that hall

% constraint forall(c in courses) (
%     card(course2halls[c]) = 1
% );

% advanced courses follow intro courses
% no slots of courses[4] are before slots of courses[3]
% no slots of courses[6] are before slots of courses[5]
% (other courses are not ordered)

constraint forall (d1 in days, d2 in days) (
    let { var set of CourseOrEmpty: c1 = day2courses[d1];
          var set of CourseOrEmpty: c2 = day2courses[d2]; }
    in
        (courses[4] in c2 /\ courses[3] in c1 -> d1 < d2) /\
        (courses[6] in c2 /\ courses[5] in c1 -> d1 < d2)
);

%

solve minimize negscore;

% output ["\(i): \(people2trajectories[i]) | (\(people2musts[i]))\n" | i in index_set(people2trajectories)] ++
    %    ["\(t): \(sum([1 | p in people where t in people2trajectories[p]]))\n" | t in trajectories] ++
       % print schedule one day per line
output ["\(d): \([schedule[p, d] | p in people])\n" | d in days] ++
       ["\n\n\n"] ++
       ["\(d): \(day2courses[d])\n" | d in days] ++
       ["\n\n\n"] ++
       ["\(c): \(course2count[c])\n" | c in courses];
    %    ["\(i) -> \(trajectories_materialized[i])\n" | i in index_set(trajectories_materialized)] ++
    %    ["Adj \(c1): \([trajectories[c1, c2] | c2 in courses])\n" | c1 in courses] ++
    %    ["Follows \(c) -> \(follows[c])\n" | c in index_set(follows)] ++
    %    ["Fail \(fail)"];
    %    ["negscore: \(negscore)"];