% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% OOCSP rack configuration example for MiniZinc Challenge 2016
% authors: Gottfried Schenner / Richard Taupe, Siemens AG Oesterreich
% A "classic" rack configuration example in MiniZinc using OOCSP
% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% OOCSP part - generic mapping from object oriented model to CSP
% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

% The aim is to generically map an object-oriented model to CSP.
% The schema of the object-oriented model is provided as parameters.
% The resulting program should be able to enumerate all possible instantiations of the object-oriented model within the given scope.
% Additional constraints can be added for finding specific instantiations.
% From the output of the program an object-oriented instantiation can be generated.
% Variant 1: based on leafclass encoding - 
% every object has a unique id and is instance of a leaf class.
%

include "increasing.mzn";
include "global_cardinality.mzn";

% 
% Encoding of class hierachy
% classnames, leafclass_min, leafclass_max are used to represent class hierarchy
% ASSUME THAT ORDER IS DEPTH FIRST LEFT TO RIGHT TRAVERSAL i.e.
%      A        B
%     / \       |
%    A1  A2     B1
%    / \      / | \
%   /   \    /  |  \
%  A11 A12 B11 B12 B13
%  classnames =    [A  , A1 , A11, A12, A2, B  , B1 , B11, B12, B13, CLASS_UNUSED]
%  leafclass_min = [A11, A11, A11, A12, A2, B11, B11, B12, B12, B13, CLASS_UNUSED]
%  leafclass_max = [A2 , A12, A11, A12, A2, B13, B13, B12, B12, B13, CLASS_UNUSED]
%
% how many classes are there
int : NROFCLASSES;
set of int : CLASSES = 1..CLASS_UNUSED;
% unused objects are of type CLASS_UNUSED
int : CLASS_UNUSED = NROFCLASSES + 1;
% how many objects can be instantiated
int : MAXNROFOBJECTS;
set of int : OBJECTS = 1..MAXNROFOBJECTS;
% reference to object or 0
set of int : OPT_OBJECT = 0..MAXNROFOBJECTS;

array[1..NROFCLASSES] of string: classnames;
array[CLASSES] of var CLASSES : leafclass_min; 
array[CLASSES] of var CLASSES : leafclass_max;
% first possible index for class
array[CLASSES] of var 1..MAXNROFOBJECTS+1 : start;
% nr of instances of class
array[CLASSES] of var 0..MAXNROFOBJECTS : nrofobjects;

% assure that start indices are ordered
constraint 
  increasing(start) /\ start[1] = 1;

% first objectid is at first leafclass object id
constraint 
  forall(c in CLASSES)
    (start[c] = start[leafclass_min[c]]);

% nrofobjects is the difference between start of first leafclass and start of next leafclass
constraint 
  forall(c in 1..NROFCLASSES)
    (nrofobjects[c] = start[leafclass_max[c]+1] - start[leafclass_min[c]]);
% the remaining objects are unused
constraint
  nrofobjects[CLASS_UNUSED] = (MAXNROFOBJECTS + 1) - start[CLASS_UNUSED];

% Object <object> is instanceof <CLASS>
predicate isA(CLASSES : CLASS, var OBJECTS : object) = 
  object >= start[leafclass_min[CLASS]] /\ object < start[leafclass_max[CLASS]+1];

% Predicates for defining the object-oriented model and writing constraints:
% Attributes are encoded as int arrays of object. If an attribute is not defined for the given object, the value is 0.
% Associations currently have two possible encodings:
% link arrays: every object has one link variable, which can either be 0 (for 0/1 assocs or if the association is not definded for this type) or 1..MAXNROFOBJECTS i.e. it "points" to another object. Link arrays can only represent 0/1-N associations; for N-M associations, link classes or set variables (see below) must be used.
% set arrays: every object has one set variable, which contains all associated objects.
% In this encoding, link arrays are used.

% ATTRIBUTES
% defines attribute for class <CLASS>
predicate hasAttribute(CLASSES: CLASS, array[OBJECTS] of var int: attributearray, int: min, int: max) =
  forall(i in OBJECTS) (if (isA(CLASS,i)) then (attributearray[i] >= min /\ attributearray[i] <= max) else attributearray[i] = 0 endif);  

% LINKARRAY ASSOCS
% defines N-1 assoc for class <CLASS> to class <LINKCLASS>
predicate hasAssocLink1(CLASSES: CLASS, array[OBJECTS] of var OPT_OBJECT: linkarray, CLASSES: LINKCLASS) =
  forall(i in OBJECTS) (if (isA(CLASS,i)) then isA(LINKCLASS, linkarray[i]) else linkarray[i] = 0 endif);

% defines N-0/1 assoc for class <CLASS> to class <LINKCLASS>
predicate hasAssocLink01(CLASSES: CLASS, array[OBJECTS] of var OPT_OBJECT: linkarray, CLASSES: LINKCLASS) =
  forall(i in OBJECTS) (if (isA(CLASS,i)) then linkarray[i]=0 \/ isA(LINKCLASS, linkarray[i]) else linkarray[i] = 0 endif);

% restrict cardinalities for N-1 assoc represented by linkarray
predicate hasAssocCardinality(array[OBJECTS] of var OPT_OBJECT: linkarray,
  array[OBJECTS] of var 0..MAXNROFOBJECTS: counts, 
  CLASSES: LINKCLASS,
  int: MINCARD,
  int: MAXCARD) =
  global_cardinality(linkarray,OBJECTS,counts) 
  /\ forall (o in OBJECTS) (if (isA(LINKCLASS,o)) then ((counts[o]>=MINCARD)/\(counts[o]<=min(MAXNROFOBJECTS,MAXCARD))) else counts[o] = 0 endif);

% define N-1 assoc with link
predicate hasAssocLink(CLASSES: CLASS1,
  int: MIN1, 
  int: MAX1,
  array[OBJECTS] of var OPT_OBJECT: role1,
  CLASSES: CLASS2,
  int: MIN2,
  int: MAX2,
  array[OBJECTS] of var 0..MAXNROFOBJECTS: count_role2, 
) =
  (if (MIN1=0) then hasAssocLink01(CLASS1,role1,CLASS2) else hasAssocLink1(CLASS1,role1,CLASS2) endif) 
  /\ hasAssocCardinality(role1,count_role2,CLASS2,MIN2,MAX2)
  ;

% isA for linkarray assoc
% all objects in the association are instances of <CLASS>
predicate isA(OBJECTS: object, array[OBJECTS] of var OPT_OBJECT: assoc, CLASSES: CLASS) = 
  forall(o in OBJECTS) (if (assoc[o] = object) then isA(CLASS,o) else true endif);

% hasNObjects for linkarray assoc
% Object <object> is associated with <min> to <max> objects of the given class in assoc <assoc>
predicate hasNObjects(OBJECTS: object, array[OBJECTS] of var OPT_OBJECT: assoc, CLASSES: class, int: min, int: max) = 
  let { var int: nrofobjects = (sum(o in OBJECTS) (assoc[o] = object /\ isA(class,o))) } in
  (nrofobjects >= min /\ nrofobjects <= max);

% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% object-oriented schema definition for rack configuration example
% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

NROFCLASSES = 16;
classnames = ["Configuration", "Element", "ElementA", "ElementB", "ElementC", "ElementD", "Frame", "Module", "ModuleI", "ModuleII", "ModuleIII", "ModuleIV", "ModuleV", "Rack", "RackDouble", "RackSingle"];
int : CLASS_Configuration = 1;
int : CLASS_Configuration_MIN;
int : CLASS_Configuration_MAX;
constraint CLASS_Configuration_MIN <= nrofobjects[CLASS_Configuration] /\ nrofobjects[CLASS_Configuration] <= CLASS_Configuration_MAX;
constraint nrofobjects[CLASS_Configuration] = 1;
int : CLASS_Element = 2;
int : CLASS_Element_MIN;
int : CLASS_Element_MAX;
constraint CLASS_Element_MIN <= nrofobjects[CLASS_Element] /\ nrofobjects[CLASS_Element] <= CLASS_Element_MAX;
int : CLASS_ElementA = 3;
int : CLASS_ElementA_MIN;
int : CLASS_ElementA_MAX;
constraint CLASS_ElementA_MIN <= nrofobjects[CLASS_ElementA] /\ nrofobjects[CLASS_ElementA] <= CLASS_ElementA_MAX;
int : CLASS_ElementB = 4;
int : CLASS_ElementB_MIN;
int : CLASS_ElementB_MAX;
constraint CLASS_ElementB_MIN <= nrofobjects[CLASS_ElementB] /\ nrofobjects[CLASS_ElementB] <= CLASS_ElementB_MAX;
int : CLASS_ElementC = 5;
int : CLASS_ElementC_MIN;
int : CLASS_ElementC_MAX;
constraint CLASS_ElementC_MIN <= nrofobjects[CLASS_ElementC] /\ nrofobjects[CLASS_ElementC] <= CLASS_ElementC_MAX;
int : CLASS_ElementD = 6;
int : CLASS_ElementD_MIN;
int : CLASS_ElementD_MAX;
constraint CLASS_ElementD_MIN <= nrofobjects[CLASS_ElementD] /\ nrofobjects[CLASS_ElementD] <= CLASS_ElementD_MAX;
int : CLASS_Frame = 7;
int : CLASS_Frame_MIN;
int : CLASS_Frame_MAX;
constraint CLASS_Frame_MIN <= nrofobjects[CLASS_Frame] /\ nrofobjects[CLASS_Frame] <= CLASS_Frame_MAX;
int : CLASS_Module = 8;
int : CLASS_Module_MIN;
int : CLASS_Module_MAX;
constraint CLASS_Module_MIN <= nrofobjects[CLASS_Module] /\ nrofobjects[CLASS_Module] <= CLASS_Module_MAX;
int : CLASS_ModuleI = 9;
int : CLASS_ModuleI_MIN;
int : CLASS_ModuleI_MAX;
constraint CLASS_ModuleI_MIN <= nrofobjects[CLASS_ModuleI] /\ nrofobjects[CLASS_ModuleI] <= CLASS_ModuleI_MAX;
int : CLASS_ModuleII = 10;
int : CLASS_ModuleII_MIN;
int : CLASS_ModuleII_MAX;
constraint CLASS_ModuleII_MIN <= nrofobjects[CLASS_ModuleII] /\ nrofobjects[CLASS_ModuleII] <= CLASS_ModuleII_MAX;
int : CLASS_ModuleIII = 11;
int : CLASS_ModuleIII_MIN;
int : CLASS_ModuleIII_MAX;
constraint CLASS_ModuleIII_MIN <= nrofobjects[CLASS_ModuleIII] /\ nrofobjects[CLASS_ModuleIII] <= CLASS_ModuleIII_MAX;
int : CLASS_ModuleIV = 12;
int : CLASS_ModuleIV_MIN;
int : CLASS_ModuleIV_MAX;
constraint CLASS_ModuleIV_MIN <= nrofobjects[CLASS_ModuleIV] /\ nrofobjects[CLASS_ModuleIV] <= CLASS_ModuleIV_MAX;
int : CLASS_ModuleV = 13;
int : CLASS_ModuleV_MIN;
int : CLASS_ModuleV_MAX;
constraint CLASS_ModuleV_MIN <= nrofobjects[CLASS_ModuleV] /\ nrofobjects[CLASS_ModuleV] <= CLASS_ModuleV_MAX;
int : CLASS_Rack = 14;
int : CLASS_Rack_MIN;
int : CLASS_Rack_MAX;
constraint CLASS_Rack_MIN <= nrofobjects[CLASS_Rack] /\ nrofobjects[CLASS_Rack] <= CLASS_Rack_MAX;
int : CLASS_RackDouble = 15;
int : CLASS_RackDouble_MIN;
int : CLASS_RackDouble_MAX;
constraint CLASS_RackDouble_MIN <= nrofobjects[CLASS_RackDouble] /\ nrofobjects[CLASS_RackDouble] <= CLASS_RackDouble_MAX;
int : CLASS_RackSingle = 16;
int : CLASS_RackSingle_MIN;
int : CLASS_RackSingle_MAX;
constraint CLASS_RackSingle_MIN <= nrofobjects[CLASS_RackSingle] /\ nrofobjects[CLASS_RackSingle] <= CLASS_RackSingle_MAX;

leafclass_min = [CLASS_Configuration, CLASS_ElementA, CLASS_ElementA, CLASS_ElementB, CLASS_ElementC, CLASS_ElementD, CLASS_Frame, CLASS_ModuleI, CLASS_ModuleI, CLASS_ModuleII, CLASS_ModuleIII, CLASS_ModuleIV, CLASS_ModuleV, CLASS_RackDouble, CLASS_RackDouble, CLASS_RackSingle, CLASS_UNUSED];
leafclass_max = [CLASS_Configuration, CLASS_ElementD, CLASS_ElementA, CLASS_ElementB, CLASS_ElementC, CLASS_ElementD, CLASS_Frame, CLASS_ModuleV, CLASS_ModuleI, CLASS_ModuleII, CLASS_ModuleIII, CLASS_ModuleIV, CLASS_ModuleV, CLASS_RackSingle, CLASS_RackDouble, CLASS_RackSingle, CLASS_UNUSED];

% Attribute Configuration.configtype
array[OBJECTS] of var 0..100: Configuration_configtype;
constraint hasAttribute(CLASS_Configuration,Configuration_configtype,1,100);

% Association Element_configuration(1,1)<->Configuration_elements(0,100)
array[OBJECTS] of var OPT_OBJECT: Element_configuration;
array[OBJECTS] of var 0..MAXNROFOBJECTS: Configuration_elements_count;
constraint hasAssocLink(CLASS_Element,1,1,Element_configuration,CLASS_Configuration,0,100,Configuration_elements_count);

% Association Frame_rack(1,1)<->Rack_frames(0,8)
array[OBJECTS] of var OPT_OBJECT: Frame_rack;
array[OBJECTS] of var 0..MAXNROFOBJECTS: Rack_frames_count;
constraint hasAssocLink(CLASS_Frame,1,1,Frame_rack,CLASS_Rack,0,8,Rack_frames_count);

% Association Module_frame(1,1)<->Frame_modules(0,6)
array[OBJECTS] of var OPT_OBJECT: Module_frame;
array[OBJECTS] of var 0..MAXNROFOBJECTS: Frame_modules_count;
constraint hasAssocLink(CLASS_Module,1,1,Module_frame,CLASS_Frame,0,6,Frame_modules_count);

% Association Module_element(0,1)<->Element_modules(0,6)
array[OBJECTS] of var OPT_OBJECT: Module_element;
array[OBJECTS] of var 0..MAXNROFOBJECTS: Element_modules_count;
constraint hasAssocLink(CLASS_Module,0,1,Module_element,CLASS_Element,0,6,Element_modules_count);

% Association Rack_configuration(1,1)<->Configuration_racks(0,100)
array[OBJECTS] of var OPT_OBJECT: Rack_configuration;
array[OBJECTS] of var 0..MAXNROFOBJECTS: Configuration_racks_count;
constraint hasAssocLink(CLASS_Rack,1,1,Rack_configuration,CLASS_Configuration,0,100,Configuration_racks_count);

output [
"%% classnames = \(classnames);\n"
++"start = \(start);\n"
++"nrofobjects = \(nrofobjects);\n"
++"Configuration_configtype = \(Configuration_configtype);\n"
++"Element_configuration = \(Element_configuration);\n"
++"Frame_rack = \(Frame_rack);\n"
++"Module_frame = \(Module_frame);\n"
++"Module_element = \(Module_element);\n"
++"Rack_configuration = \(Rack_configuration);\n"
];

% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% Additional constraints:
% RackSingle has 4 Frames
% RackDouble has 8 Frames
% ElementA requires 1 ModuleI
% ElementB requires 2 ModuleII
% ElementC requires 3 ModuleIII
% ElementD requires 4 ModuleIV
% ModuleV can have no Elements. 
% Whenever a ModuleII is inside a frame, there must also be one ModuleV in the frame
% All modules of one element must be in the same frame 
% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

% constraint for configtype1
% root class
constraint
  nrofobjects[CLASS_Configuration] = 1;

% element<->module
constraint
  forall (o in OBJECTS where isA(CLASS_ElementA,o)) (hasNObjects(o,Module_element,CLASS_Module,1,1));

constraint
  forall (o in OBJECTS where isA(CLASS_ElementA,o)) (isA(o,Module_element,CLASS_ModuleI));

% element<->module
constraint
  forall (o in OBJECTS where isA(CLASS_ElementB,o)) (hasNObjects(o,Module_element,CLASS_Module,2,2));

constraint
  forall (o in OBJECTS where isA(CLASS_ElementB,o)) (isA(o,Module_element,CLASS_ModuleII));

% element<->module
constraint
  forall (o in OBJECTS where isA(CLASS_ElementC,o)) (hasNObjects(o,Module_element,CLASS_Module,3,3));

constraint
  forall (o in OBJECTS where isA(CLASS_ElementC,o)) (isA(o,Module_element,CLASS_ModuleIII));

% element<->module
constraint
  forall (o in OBJECTS where isA(CLASS_ElementD,o)) (hasNObjects(o,Module_element,CLASS_Module,4,4));

constraint
  forall (o in OBJECTS where isA(CLASS_ElementD,o)) (isA(o,Module_element,CLASS_ModuleIV));

% moduleV has no element
constraint
  forall (o in OBJECTS where isA(CLASS_Element,o)) (hasNObjects(o,Module_element,CLASS_ModuleV,0,0));

% all other modules have an element
constraint
  forall(o in OBJECTS where isA(CLASS_ModuleI,o) \/ isA(CLASS_ModuleII,o) \/ isA(CLASS_ModuleIII,o) \/ isA(CLASS_ModuleIV,o)) 
    (Module_element[o] > 0);

% constraints for moduleV
constraint
  forall (o1 in OBJECTS where isA(CLASS_ModuleII,o1)) 
    (exists (o2 in OBJECTS) (isA(CLASS_ModuleV,o2) /\ Module_frame[o1]=Module_frame[o2]));

% all modules of an element must be in the same frame
constraint
  forall (o1,o2 in OBJECTS where isA(CLASS_Module,o1) /\ isA(CLASS_Module,o2) /\ o1!=o2) 
    (if ((Module_element[o1]!=0)/\(Module_element[o1]=Module_element[o2])) then (Module_frame[o1]=Module_frame[o2]) else true endif);

% racks<->frame constraint
constraint
  forall (o in OBJECTS where isA(CLASS_RackSingle,o)) (hasNObjects(o,Frame_rack,CLASS_Frame,4,4));

constraint
  forall (o in OBJECTS where isA(CLASS_RackDouble,o)) (hasNObjects(o,Frame_rack,CLASS_Frame,8,8));

bool: USECARDINALITYCONSTRAINTS;

constraint
if USECARDINALITYCONSTRAINTS then
% manual
nrofobjects[CLASS_Frame]>=nrofobjects[CLASS_RackSingle]*4 /\
nrofobjects[CLASS_Frame]>=nrofobjects[CLASS_RackDouble]*8 /\
% automatic
0*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_Element]<=0 /\
1*nrofobjects[CLASS_ElementC] + -1*nrofobjects[CLASS_Element]<=0 /\
0*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_RackDouble] + -1*nrofobjects[CLASS_RackSingle]<=0 /\
1*nrofobjects[CLASS_ElementA] + 1*nrofobjects[CLASS_ElementB] + 1*nrofobjects[CLASS_ElementC] + 1*nrofobjects[CLASS_ElementD] + -1*nrofobjects[CLASS_Element]=0 /\
1*nrofobjects[CLASS_ElementB] + -1*nrofobjects[CLASS_Element]<=0 /\
1*nrofobjects[CLASS_ModuleIV] + -1*nrofobjects[CLASS_Module]<=0 /\
1*nrofobjects[CLASS_ModuleI] + 1*nrofobjects[CLASS_ModuleII] + 1*nrofobjects[CLASS_ModuleIII] + 1*nrofobjects[CLASS_ModuleIV] + 1*nrofobjects[CLASS_ModuleV] + -1*nrofobjects[CLASS_Module]=0 /\
1*nrofobjects[CLASS_ElementA] + -1*nrofobjects[CLASS_Element]<=0 /\
0*nrofobjects[CLASS_Module] + -6*nrofobjects[CLASS_ElementA] + -6*nrofobjects[CLASS_ElementC] + -6*nrofobjects[CLASS_ElementD] + -6*nrofobjects[CLASS_ElementB]<=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_ElementD]<=0 /\
0*nrofobjects[CLASS_Module] + -1*nrofobjects[CLASS_ModuleIV]<=0 /\
1*nrofobjects[CLASS_ModuleIII] + -1*nrofobjects[CLASS_Module]<=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_ModuleIV] + -1*nrofobjects[CLASS_ModuleIII] + -1*nrofobjects[CLASS_ModuleII] + -1*nrofobjects[CLASS_ModuleI] + -1*nrofobjects[CLASS_ModuleV]<=0 /\
0*nrofobjects[CLASS_Module] + -1*nrofobjects[CLASS_ModuleI]<=0 /\
1*nrofobjects[CLASS_ModuleII] + -1*nrofobjects[CLASS_Module]<=0 /\
1*nrofobjects[CLASS_Configuration]<=1 /\
1*nrofobjects[CLASS_Frame] + -8*nrofobjects[CLASS_RackSingle] + -8*nrofobjects[CLASS_RackDouble]<=0 /\
1*nrofobjects[CLASS_Module] + -6*nrofobjects[CLASS_Frame]<=0 /\
1*nrofobjects[CLASS_ElementD] + -1*nrofobjects[CLASS_Element]<=0 /\
1*nrofobjects[CLASS_RackSingle] + 1*nrofobjects[CLASS_RackDouble] + -1*nrofobjects[CLASS_Rack]=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_ElementB]<=0 /\
6*nrofobjects[CLASS_Element] + 0*nrofobjects[CLASS_ModuleV] + 0*nrofobjects[CLASS_ModuleIV] + 0*nrofobjects[CLASS_ModuleI] + 0*nrofobjects[CLASS_ModuleII] + 0*nrofobjects[CLASS_ModuleIII]>=0 /\
0*nrofobjects[CLASS_Rack] + -1*nrofobjects[CLASS_Frame]<=0 /\
1*nrofobjects[CLASS_ModuleV] + -1*nrofobjects[CLASS_Module]<=0 /\
0*nrofobjects[CLASS_Module] + -6*nrofobjects[CLASS_Element]<=0 /\
1*nrofobjects[CLASS_ModuleI] + -1*nrofobjects[CLASS_Module]<=0 /\
1*nrofobjects[CLASS_Module] + 0*nrofobjects[CLASS_ElementD] + 0*nrofobjects[CLASS_ElementA] + 0*nrofobjects[CLASS_ElementB] + 0*nrofobjects[CLASS_ElementC]>=0 /\
100*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_RackSingle] + -1*nrofobjects[CLASS_RackDouble]>=0 /\
100*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_ElementA] + -1*nrofobjects[CLASS_ElementC] + -1*nrofobjects[CLASS_ElementB] + -1*nrofobjects[CLASS_ElementD]>=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_Module]<=0 /\
0*nrofobjects[CLASS_Frame] + -1*nrofobjects[CLASS_Module]<=0 /\
1*nrofobjects[CLASS_Frame] + 0*nrofobjects[CLASS_RackSingle] + 0*nrofobjects[CLASS_RackDouble]>=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_ElementA]<=0 /\
0*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_ElementB] + -1*nrofobjects[CLASS_ElementC] + -1*nrofobjects[CLASS_ElementD] + -1*nrofobjects[CLASS_ElementA]<=0 /\
0*nrofobjects[CLASS_Frame] + -1*nrofobjects[CLASS_ModuleV] + -1*nrofobjects[CLASS_ModuleIV] + -1*nrofobjects[CLASS_ModuleII] + -1*nrofobjects[CLASS_ModuleI] + -1*nrofobjects[CLASS_ModuleIII]<=0 /\
1*nrofobjects[CLASS_Rack] + -100*nrofobjects[CLASS_Configuration]<=0 /\
1*nrofobjects[CLASS_RackSingle] + -1*nrofobjects[CLASS_Rack]<=0 /\
0*nrofobjects[CLASS_Module] + -1*nrofobjects[CLASS_ModuleII]<=0 /\
6*nrofobjects[CLASS_Frame] + -1*nrofobjects[CLASS_ModuleI] + -1*nrofobjects[CLASS_ModuleIV] + -1*nrofobjects[CLASS_ModuleIII] + -1*nrofobjects[CLASS_ModuleV] + -1*nrofobjects[CLASS_ModuleII]>=0 /\
0*nrofobjects[CLASS_Element] + -1*nrofobjects[CLASS_ElementC]<=0 /\
1*nrofobjects[CLASS_Element] + -100*nrofobjects[CLASS_Configuration]<=0 /\
0*nrofobjects[CLASS_Module] + -1*nrofobjects[CLASS_ModuleIII]<=0 /\
1*nrofobjects[CLASS_Configuration]>=1 /\
0*nrofobjects[CLASS_Rack] + -1*nrofobjects[CLASS_RackDouble]<=0 /\
1*nrofobjects[CLASS_Frame] + -8*nrofobjects[CLASS_Rack]<=0 /\
0*nrofobjects[CLASS_Rack] + -1*nrofobjects[CLASS_RackSingle]<=0 /\
0*nrofobjects[CLASS_Module] + -1*nrofobjects[CLASS_ModuleV]<=0 /\
1*nrofobjects[CLASS_RackDouble] + -1*nrofobjects[CLASS_Rack]<=0 /\
0*nrofobjects[CLASS_Configuration] + -1*nrofobjects[CLASS_Rack]<=0
else
true
endif;

% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% Parameters
% +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
% 
%USECARDINALITYCONSTRAINTS = true;
% how many objects can be instantiated
%MAXNROFOBJECTS = 5; 
% CLASS_<CLASSNAME>_MIN/MAX min/max number of instances of <CLASS>
% e.g. to find a configuration with 5 element and at most 20 instances set 
% MAXNROFOBJECTS = 20 CLASS_Element_MIN = 5 CLASS_Element_MAX = 5 
%CLASS_Configuration_MIN = 0;
%CLASS_Configuration_MAX = MAXNROFOBJECTS;
%CLASS_Element_MIN = 0;
%CLASS_Element_MAX = MAXNROFOBJECTS;
%CLASS_ElementA_MIN = 0;
%CLASS_ElementA_MAX = MAXNROFOBJECTS;
%CLASS_ElementB_MIN = 0;
%CLASS_ElementB_MAX = MAXNROFOBJECTS;
%CLASS_ElementC_MIN = 0;
%CLASS_ElementC_MAX = MAXNROFOBJECTS;
%CLASS_ElementD_MIN = 0;
%CLASS_ElementD_MAX = MAXNROFOBJECTS;
%CLASS_Frame_MIN = 0;
%CLASS_Frame_MAX = MAXNROFOBJECTS;
%CLASS_Module_MIN = 0;
%CLASS_Module_MAX = MAXNROFOBJECTS;
%CLASS_ModuleI_MIN = 0;
%CLASS_ModuleI_MAX = MAXNROFOBJECTS;
%CLASS_ModuleII_MIN = 0;
%CLASS_ModuleII_MAX = MAXNROFOBJECTS;
%CLASS_ModuleIII_MIN = 0;
%CLASS_ModuleIII_MAX = MAXNROFOBJECTS;
%CLASS_ModuleIV_MIN = 0;
%CLASS_ModuleIV_MAX = MAXNROFOBJECTS;
%CLASS_ModuleV_MIN = 0;
%CLASS_ModuleV_MAX = MAXNROFOBJECTS;
%CLASS_Rack_MIN = 0;
%CLASS_Rack_MAX = MAXNROFOBJECTS;
%CLASS_RackDouble_MIN = 0;
%CLASS_RackDouble_MAX = MAXNROFOBJECTS;
%CLASS_RackSingle_MIN = 0;
%CLASS_RackSingle_MAX = MAXNROFOBJECTS;

solve 
% this heuristic will not enhance performance, but fix the domains (cf. http://www.minizinc.org/challenge2016/rules2016.html, problem format restriction 4)
::int_search(nrofobjects ++ Configuration_configtype ++ Frame_rack ++ Module_frame ++ Module_element ++ Rack_configuration ++ Element_configuration , input_order, indomain_min,complete)

satisfy;
