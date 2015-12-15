// Global Vars
var ghost;

var timeStep = 1.0 / 60.0;

var doDraw = true;
var cw_paused = false;

var box2dfps = 60;
var screenfps = 60;

var debugbox = document.getElementById("debug");

var canvas = document.getElementById("mainbox");
var ctx = canvas.getContext("2d");

var cameraspeed = 0.05;
var camera_y = 0;
var camera_x = 0;
var camera_target = -1; // which car should we follow? -1 = leader
var minimapcamera = document.getElementById("minimapcamera").style;

var graphcanvas = document.getElementById("graphcanvas");
var graphctx = graphcanvas.getContext("2d");
var graphheight = 250;
var graphwidth = 400;

var minimapcanvas = document.getElementById("minimap");
var minimapctx = minimapcanvas.getContext("2d");
var minimapscale = 3;
var minimapfogdistance = 0;
var fogdistance = document.getElementById("minimapfog").style;

var generationSize = 20;

/**
 * The current array of cars.
 */
var cw_carArray = new Array();

/**
 * The array containing the genome of each car in a generation
 */
var cw_carGeneration = new Array();

/**
 * car_def:this.car_def, v:score, s: avgspeed, x:position, y:this.maxPositiony, y2:this.minPositiony
 */
var cw_carScores = new Array();

var cw_topScores = new Array();
var cw_graphTop = new Array();
var cw_graphElite = new Array();
var cw_graphAverage = new Array();

/**
 * How many elite champions are stored.
 */
var gen_champions = 1;
var gen_parentality = 0.2;
var gen_mutation = 0.05;
var mutation_range = 1;
var gen_counter = 0;
var nAttributes = 15;

var gravity = new b2Vec2(0.0, -9.81);
var doSleep = true;

var world;

var zoom = 70;

var mutable_floor = false;

var maxFloorTiles = 200;
var cw_floorTiles = new Array();
var last_drawn_tile = 0;

var groundPieceWidth = 1.5;
var groundPieceHeight = 0.15;

var chassisMaxAxis = 1.1;
var chassisMinAxis = 0.2;
var chassisMinDensity = 30;
var chassisMaxDensity = 300;

var wheelMaxRadius = 0.5;
var wheelMinRadius = 0.2;
var wheelMaxDensity = 100;
var wheelMinDensity = 40;

var velocityIndex = 0;
var deathSpeed = 0.1;
var max_car_health = box2dfps * 10;
var car_health = max_car_health;

var motorSpeed = 20;

var swapPoint1 = 0;
var swapPoint2 = 0;

var cw_ghostReplayInterval = null;

var distanceMeter = document.getElementById("distancemeter");

/**
 * The last given ID of a gene.
 */
var geneId = 0;

var leaderPosition = new Object();
leaderPosition.x = 0;
leaderPosition.y = 0;

minimapcamera.width = 12*minimapscale+"px";
minimapcamera.height = 6*minimapscale+"px";

function debug(str, clear) {
  if(clear) {
    debugbox.innerHTML = "";
  }
  debugbox.innerHTML += str+"<br />";
}

function showDistance(distance, height) {
  distanceMeter.innerHTML = "distance: "+distance+" meters<br />";
  distanceMeter.innerHTML += "height: "+height+" meters";
  if(distance > minimapfogdistance) {
    fogdistance.width = 800 - Math.round(distance + 15) * minimapscale + "px";
    minimapfogdistance = distance;
  }
}

/* ========================================================================= */
/* === Car ================================================================= */
var cw_Car = function() {
  this.__constructor.apply(this, arguments);
}

cw_Car.prototype.chassis = null;

cw_Car.prototype.wheels = [];

cw_Car.prototype.__constructor = function(car_def) {
  this.velocityIndex = 0;
  this.health = max_car_health;
  this.maxPosition = 0;
  this.maxPositiony = 0;
  this.minPositiony = 0;
  this.frames = 0;
  this.car_def = car_def
  this.alive = true;
  this.is_elite = car_def.is_elite;
  this.healthBar = document.getElementById("health"+car_def.index).style;
  this.healthBarText = document.getElementById("health"+car_def.index).nextSibling.nextSibling;
  this.healthBarText.innerHTML = car_def.index.toString();
  this.healthBarGene = document.getElementById("health"+car_def.index).nextSibling.nextSibling.nextSibling.nextSibling;
  this.healthBarGene.innerHTML = printGeneId(car_def.genome);
  this.minimapmarker = document.getElementById("bar"+car_def.index);

  if(this.is_elite) {
    this.healthBar.backgroundColor = "#44c";
    this.minimapmarker.style.borderLeft = "1px solid #44c";
    this.minimapmarker.innerHTML = car_def.index;
  } else {
    this.healthBar.backgroundColor = "#c44";
    this.minimapmarker.style.borderLeft = "1px solid #c44";
    this.minimapmarker.innerHTML = car_def.index;
  }

  this.chassis = cw_createChassis(car_def.vertex_list, car_def.chassis_density);
  
  this.wheels = [];
  for (var i = 0; i < car_def.wheelCount; i++){
    this.wheels[i] = cw_createWheel(car_def.wheel_radius[i], car_def.wheel_density[i]);
  }
  
  var carmass = this.chassis.GetMass();
  for (var i = 0; i < car_def.wheelCount; i++){
    carmass += this.wheels[i].GetMass();
  }
  var torque = [];
  for (var i = 0; i < car_def.wheelCount; i++){
    torque[i] = carmass * -gravity.y / car_def.wheel_radius[i];
  }
  
  var joint_def = new b2RevoluteJointDef();

  for (var i = 0; i < car_def.wheelCount; i++){
    var randvertex = this.chassis.vertex_list[car_def.wheel_vertex[i]];
    joint_def.localAnchorA.Set(randvertex.x, randvertex.y);
    joint_def.localAnchorB.Set(0, 0);
    joint_def.maxMotorTorque = torque[i];
    joint_def.motorSpeed = -motorSpeed;
    joint_def.enableMotor = true;
    joint_def.bodyA = this.chassis;
    joint_def.bodyB = this.wheels[i];
    var joint = world.CreateJoint(joint_def);
  }
  
  this.replay = ghost_create_replay();
  ghost_add_replay_frame(this.replay, this);
}

cw_Car.prototype.getPosition = function() {
  return this.chassis.GetPosition();
}

cw_Car.prototype.draw = function() {
  drawObject(this.chassis);
  
  for (var i = 0; i < this.wheels.length; i++){
    drawObject(this.wheels[i]);
  }
}

cw_Car.prototype.kill = function() {
  var avgspeed = (this.maxPosition / this.frames) * box2dfps;
  var position = this.maxPosition;
  var score = position + avgspeed;
  ghost_compare_to_replay(this.replay, ghost, score);
  cw_carScores.push({ car_def:this.car_def, v:score, s: avgspeed, x:position, y:this.maxPositiony, y2:this.minPositiony });
  world.DestroyBody(this.chassis);
  
  for (var i = 0; i < this.wheels.length; i++){
    world.DestroyBody(this.wheels[i]);
  }
  this.alive = false;
  
  // refocus camera to leader on death
  if (camera_target == this.car_def.index){
    cw_setCameraTarget(-1);
  }
}

cw_Car.prototype.checkDeath = function() {
  // check health
  var position = this.getPosition();
  if(position.y > this.maxPositiony) {
    this.maxPositiony = position.y;
  }
  if(position .y < this.minPositiony) {
    this.minPositiony = position.y;
  }
  if(position.x > this.maxPosition + 0.02) {
    this.health = max_car_health;
    this.maxPosition = position.x;
  } else {
    if(position.x > this.maxPosition) {
      this.maxPosition = position.x;
    }
    if(Math.abs(this.chassis.GetLinearVelocity().x) < 0.001) {
      this.health -= 5;
    }
    this.health--;
    if(this.health <= 0) {
      this.healthBarText.innerHTML = "&#8708;";
      this.healthBar.width = "0";
      return true;
    }
  }
}

function cw_createChassisPart(body, vertex1, vertex2, density) {
  var vertex_list = new Array();
  vertex_list.push(vertex1);
  vertex_list.push(vertex2);
  vertex_list.push(b2Vec2.Make(0,0));
  var fix_def = new b2FixtureDef();
  fix_def.shape = new b2PolygonShape();
  fix_def.density = density;
  fix_def.friction = 10;
  fix_def.restitution = 0.2;
  fix_def.filter.groupIndex = -1;
  fix_def.shape.SetAsArray(vertex_list,3);

  body.CreateFixture(fix_def);
}

function cw_createChassis(vertex_list, density) {
  var body_def = new b2BodyDef();
  body_def.type = b2Body.b2_dynamicBody;
  body_def.position.Set(0.0, 4.0);

  var body = world.CreateBody(body_def);

  cw_createChassisPart(body, vertex_list[0], vertex_list[1], density);
  cw_createChassisPart(body, vertex_list[1], vertex_list[2], density);
  cw_createChassisPart(body, vertex_list[2], vertex_list[3], density);
  cw_createChassisPart(body, vertex_list[3], vertex_list[4], density);
  cw_createChassisPart(body, vertex_list[4], vertex_list[5], density);
  cw_createChassisPart(body, vertex_list[5], vertex_list[6], density);
  cw_createChassisPart(body, vertex_list[6], vertex_list[7], density);
  cw_createChassisPart(body, vertex_list[7], vertex_list[0], density);

  body.vertex_list = vertex_list;

  return body;
}

function cw_createWheel(radius, density) {
  var body_def = new b2BodyDef();
  body_def.type = b2Body.b2_dynamicBody;
  body_def.position.Set(0, 0);

  var body = world.CreateBody(body_def);

  var fix_def = new b2FixtureDef();
  fix_def.shape = new b2CircleShape(radius);
  fix_def.density = density;
  fix_def.friction = 1;
  fix_def.restitution = 0.2;
  fix_def.filter.groupIndex = -1;

  body.CreateFixture(fix_def);
  return body;
}

function cw_createRandomGene() {
  var gene_def = new Object();
  
  gene_def.id = geneId++;
  
  gene_def.wheel_radius_1  = 0.0;
  gene_def.wheel_density_1 = 0.0;
  gene_def.wheel_vertex_1  = 0.0;
  gene_def.wheel_radius_2  = 0.0;
  gene_def.wheel_density_2 = 0.0;
  gene_def.wheel_vertex_2  = 0.0;
  
  gene_def.chassis_density = 0.0;

  gene_def.vertex_list_1   = 0.0;
  gene_def.vertex_list_2   = 0.0;
  gene_def.vertex_list_3   = 0.0;
  gene_def.vertex_list_4   = 0.0;
  gene_def.vertex_list_5   = 0.0;
  gene_def.vertex_list_6   = 0.0;
  gene_def.vertex_list_7   = 0.0;
  gene_def.vertex_list_8   = 0.0;
  gene_def.vertex_list_9   = 0.0;
  gene_def.vertex_list_A   = 0.0;
  gene_def.vertex_list_B   = 0.0;
  gene_def.vertex_list_C   = 0.0;
  
  if(Math.random()<0.1) gene_def.wheel_radius_1  = (Math.random()*1.5*wheelMaxRadius-(wheelMaxRadius*0.5));
  if(Math.random()<0.1) gene_def.wheel_density_1 = (Math.random()*1.5*wheelMaxDensity-(wheelMaxDensity*0.5));
  if(Math.random()<0.1) gene_def.wheel_vertex_1  = Math.floor(Math.random()*8);
  if(Math.random()<0.1) gene_def.wheel_radius_2  = (Math.random()*1.5*wheelMaxRadius-(wheelMaxRadius*0.5));
  if(Math.random()<0.1) gene_def.wheel_density_2 = (Math.random()*1.5*wheelMaxDensity-(wheelMaxDensity*0.5));
  if(Math.random()<0.1) gene_def.wheel_vertex_2  = Math.floor(Math.random()*8);
  
  if(Math.random()<0.1) gene_def.chassis_density = (Math.random()*1.5*chassisMaxDensity-(chassisMaxDensity*0.5));

  if(Math.random()<0.1) gene_def.vertex_list_1   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_2   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_3   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_4   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_5   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_6   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_7   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_8   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_9   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_A   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_B   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));
  if(Math.random()<0.1) gene_def.vertex_list_C   = (Math.random()*1.5*chassisMaxAxis-(chassisMaxAxis*0.5));

  return gene_def;
}

function printGeneId(genome) {
	var str = genome.length.toString()+"[";
	var comma = false;
	for(var i=0; i<genome.length; i++) {
		if(comma) str += ",";
		str += genome[i].id.toString();
		comma=true;
	}
	str += "]";
	return str;
}

function cw_genomeToCarDef(genome) {
  var wheel_radius_1  = 0.0;
  var wheel_radius_2  = 0.0;
  var wheel_density_1 = 0.0;
  var wheel_density_2 = 0.0;
  //var wheel_vertex_vote1 = new Array();
  //var wheel_vertex_vote2 = new Array();
  //for(var i=0; i<8; i++) {
  //  wheel_vertex_vote1[i] = 0;
  //  wheel_vertex_vote2[i] = 0;
  // }
  var chassis_density = 0.0;
  var vertex_list_1   = 0.0;
  var vertex_list_2   = 0.0;
  var vertex_list_3   = 0.0;
  var vertex_list_4   = 0.0;
  var vertex_list_5   = 0.0;
  var vertex_list_6   = 0.0;
  var vertex_list_7   = 0.0;
  var vertex_list_8   = 0.0;
  var vertex_list_9   = 0.0;
  var vertex_list_A   = 0.0;
  var vertex_list_B   = 0.0;
  var vertex_list_C   = 0.0;
  
  for(var i=0; i<genome.length; i++) {
  	wheel_radius_1 += genome[i].wheel_radius_1;
  	wheel_radius_2 += genome[i].wheel_radius_2;
  	wheel_density_1 += genome[i].wheel_density_1;
  	wheel_density_2 += genome[i].wheel_density_2;
  	//wheel_vertex_vote1[genome[i].wheel_vertex_1]++;
  	//wheel_vertex_vote2[genome[i].wheel_vertex_2]++;
  	chassis_density += genome[i].chassis_density;
  	vertex_list_1 += genome[i].vertex_list_1;
  	vertex_list_2 += genome[i].vertex_list_2;
  	vertex_list_3 += genome[i].vertex_list_3;
  	vertex_list_4 += genome[i].vertex_list_4;
  	vertex_list_5 += genome[i].vertex_list_5;
  	vertex_list_6 += genome[i].vertex_list_6;
  	vertex_list_7 += genome[i].vertex_list_7;
  	vertex_list_8 += genome[i].vertex_list_8;
  	vertex_list_9 += genome[i].vertex_list_9;
  	vertex_list_A += genome[i].vertex_list_A;
  	vertex_list_B += genome[i].vertex_list_B;
  	vertex_list_C += genome[i].vertex_list_C;
  }
  
  if(wheel_radius_1>wheelMaxRadius) wheel_radius_1 = wheelMaxRadius;
  if(wheel_radius_2>wheelMaxRadius) wheel_radius_2 = wheelMaxRadius;
  if(wheel_density_1>wheelMaxDensity) wheel_density_1 = wheelMaxDensity;
  if(wheel_density_2>wheelMaxDensity) wheel_density_2 = wheelMaxDensity;
  if(wheel_radius_1<wheelMinRadius) wheel_radius_1 = wheelMinRadius;
  if(wheel_radius_2<wheelMinRadius) wheel_radius_2 = wheelMinRadius;
  if(wheel_density_1<wheelMinDensity) wheel_density_1 = wheelMinDensity;
  if(wheel_density_2<wheelMinDensity) wheel_density_2 = wheelMinDensity;
  var wheel_vertex_1 = genome[0].wheel_vertex_1;
  var wheel_vertex_2 = genome[1].wheel_vertex_2;
  //for(var i=1; i<8; i++) {
  //	if(wheel_vertex_vote1[i]>wheel_vertex_vote1[wheel_vertex_1] && wheel_vertex_2!=i) wheel_vertex_1 = i;
  //	if(wheel_vertex_vote2[i]>wheel_vertex_vote2[wheel_vertex_2] && wheel_vertex_1!=i) wheel_vertex_2 = i;
  //}
  if(chassis_density>chassisMaxDensity) chassis_density = chassisMaxDensity;
  if(chassis_density<chassisMinDensity) chassis_density = chassisMinDensity;
  if(vertex_list_1>chassisMaxAxis) vertex_list_1 = chassisMaxAxis;
  if(vertex_list_2>chassisMaxAxis) vertex_list_2 = chassisMaxAxis;
  if(vertex_list_3>chassisMaxAxis) vertex_list_3 = chassisMaxAxis;
  if(vertex_list_4>chassisMaxAxis) vertex_list_4 = chassisMaxAxis;
  if(vertex_list_5>chassisMaxAxis) vertex_list_5 = chassisMaxAxis;
  if(vertex_list_6>chassisMaxAxis) vertex_list_6 = chassisMaxAxis;
  if(vertex_list_7>chassisMaxAxis) vertex_list_7 = chassisMaxAxis;
  if(vertex_list_8>chassisMaxAxis) vertex_list_8 = chassisMaxAxis;
  if(vertex_list_9>chassisMaxAxis) vertex_list_9 = chassisMaxAxis;
  if(vertex_list_A>chassisMaxAxis) vertex_list_A = chassisMaxAxis;
  if(vertex_list_B>chassisMaxAxis) vertex_list_B = chassisMaxAxis;
  if(vertex_list_C>chassisMaxAxis) vertex_list_C = chassisMaxAxis;
  if(vertex_list_1<0.0) vertex_list_1 = 0.0;  
  if(vertex_list_2<0.0) vertex_list_2 = 0.0;  
  if(vertex_list_3<0.0) vertex_list_3 = 0.0;  
  if(vertex_list_4<0.0) vertex_list_4 = 0.0;  
  if(vertex_list_5<0.0) vertex_list_5 = 0.0;  
  if(vertex_list_6<0.0) vertex_list_6 = 0.0;  
  if(vertex_list_7<0.0) vertex_list_7 = 0.0;  
  if(vertex_list_8<0.0) vertex_list_8 = 0.0;  
  if(vertex_list_9<0.0) vertex_list_9 = 0.0;  
  if(vertex_list_A<0.0) vertex_list_A = 0.0;  
  if(vertex_list_B<0.0) vertex_list_B = 0.0;  
  if(vertex_list_C<0.0) vertex_list_C = 0.0;
  
  var car_def = new Object();
  car_def.genome = genome;
  car_def.wheelCount = 2;
  car_def.wheel_radius = [];
  car_def.wheel_density = [];
  car_def.wheel_vertex = [];
  car_def.wheel_radius.push(wheel_radius_1);
  car_def.wheel_radius.push(wheel_radius_2);
  car_def.wheel_density.push(wheel_density_1);
  car_def.wheel_density.push(wheel_density_2);
  car_def.wheel_vertex.push(wheel_vertex_1);
  car_def.wheel_vertex.push(wheel_vertex_2);
  car_def.chassis_density = chassis_density;
  car_def.vertex_list = new Array();
  car_def.vertex_list.push(new b2Vec2( vertex_list_1 + chassisMinAxis,  0));
  car_def.vertex_list.push(new b2Vec2( vertex_list_2 + chassisMinAxis,  vertex_list_3 + chassisMinAxis));
  car_def.vertex_list.push(new b2Vec2(0,                                vertex_list_4 + chassisMinAxis));
  car_def.vertex_list.push(new b2Vec2(-vertex_list_5 - chassisMinAxis,  vertex_list_6 + chassisMinAxis));
  car_def.vertex_list.push(new b2Vec2(-vertex_list_7 - chassisMinAxis,  0));
  car_def.vertex_list.push(new b2Vec2(-vertex_list_8 - chassisMinAxis, -vertex_list_9 - chassisMinAxis));
  car_def.vertex_list.push(new b2Vec2(0,                               -vertex_list_A - chassisMinAxis));
  car_def.vertex_list.push(new b2Vec2( vertex_list_B + chassisMinAxis, -vertex_list_C - chassisMinAxis));

  return car_def;
}

function cw_createRandomCar() {
  genome = new Array();
  for (var i = 0; i<20; i++) {
  	genome.push(cw_createRandomGene());
  }
  
  return(cw_genomeToCarDef(genome));
}

/* === END Car ============================================================= */
/* ========================================================================= */


/* ========================================================================= */
/* ==== Generation ========================================================= */

function cw_generationZero() {
  for(var k = 0; k < generationSize; k++) {
    var car_def = cw_createRandomCar();
    car_def.index = k;
    cw_carGeneration.push(car_def);
  }
  gen_counter = 0;
  cw_deadCars = 0;
  leaderPosition = new Object();
  leaderPosition.x = 0;
  leaderPosition.y = 0;
  cw_materializeGeneration();
  document.getElementById("generation").innerHTML = "generation 0";
  document.getElementById("population").innerHTML = "cars alive: "+generationSize;
  ghost = ghost_create_ghost();
}

function cw_materializeGeneration() {
  cw_carArray = new Array();
  for(var k = 0; k < generationSize; k++) {
    cw_carArray.push(new cw_Car(cw_carGeneration[k]));
  }
}

function cw_nextGeneration() {
  var newGeneration = new Array();
  var newborn;
  cw_getChampions();
  cw_topScores.push({i:gen_counter,v:cw_carScores[0].v,x:cw_carScores[0].x,y:cw_carScores[0].y,y2:cw_carScores[0].y2});
  plot_graphs();
  for(var k = 0; k < gen_champions; k++) {			// Copy the elite cars to the next generation
    cw_carScores[k].car_def.is_elite = true;
    cw_carScores[k].car_def.index = k;
    newGeneration.push(cw_carScores[k].car_def);
  }
  for(k = gen_champions; k < generationSize; k++) {	// Mate the cars to create the rest of the new generation
    var parent1 = cw_getParents();
    var parent2 = parent1;
    while(parent2 == parent1) {
      parent2 = cw_getParents();
    }
    newborn = cw_makeChild(cw_carScores[parent1].car_def,
                           cw_carScores[parent2].car_def);
    newborn.is_elite = false;
    newborn.index = k;
    newGeneration.push(newborn);
  }
  cw_carScores = new Array();
  cw_carGeneration = newGeneration;
  gen_counter++;
  cw_materializeGeneration();
  cw_deadCars = 0;
  leaderPosition = new Object();
  leaderPosition.x = 0;
  leaderPosition.y = 0;
  document.getElementById("generation").innerHTML = "generation "+gen_counter;
  document.getElementById("cars").innerHTML = "";
  document.getElementById("population").innerHTML = "cars alive: "+generationSize;
}

function cw_getChampions() {
  var ret = new Array();
  cw_carScores.sort(function(a,b) {if(a.v > b.v) {return -1} else {return 1}});
  for(var k = 0; k < generationSize; k++) {
    ret.push(cw_carScores[k].i);
  }
  return ret;
}

/**
 * The best placed cars are the preferred options for parents.
 */
function cw_getParents() {
	var ret = 0;
	while(Math.random()>0.5 && ret<generationSize-1) {
		ret++;
	}
    return ret;
}

function cw_makeChild(car_def1, car_def2) {
  var genome1 = car_def1.genome;
  var genome2 = car_def2.genome;
  var new_genome = new Array();
  var genome_length = genome1.length;
  if(genome2.length>genome_length) genome_length = genome2.length;
  for(var i=0; i<genome_length; i++) {
  	if(Math.random()>0.5 && genome1.length>i) new_genome.push(genome1[i]);
  	else if(genome2.length>i) new_genome.push(genome2[i]);
  	if(Math.random() < gen_mutation) new_genome[i] = cw_createRandomGene();
  }
  if(Math.random() < gen_mutation) new_genome.push(cw_createRandomGene());
  if(Math.random() < gen_mutation && new_genome.length>20) {
  	var victim = Math.floor(Math.random()*new_genome.length);
  	new_genome.splice(victim, 1);
  }

  return cw_genomeToCarDef(new_genome);
}

function cw_chooseParent(curparent, attributeIndex) {
  var ret;
  if((swapPoint1 == attributeIndex) || (swapPoint2 == attributeIndex)) {
    if(curparent == 1) {
      ret = 0;
    } else {
      ret = 1;
    }
  } else {
    ret = curparent;
  }
  return ret;
}

function cw_setMutation(mutation) {
  gen_mutation = parseFloat(mutation);
}

function cw_setMutationRange(range) {
  mutation_range = parseFloat(range);
}

function cw_setMutableFloor(choice) {
  mutable_floor = (choice==1);
}

function cw_setGravity(choice) {
  gravity = new b2Vec2(0.0, -parseFloat(choice));
  // CHECK GRAVITY CHANGES
  if (world.GetGravity().y != gravity.y) {
    world.SetGravity(gravity);
  }
}

function cw_setEliteSize(clones) {
  gen_champions = parseInt(clones, 10);
}

/* ==== END Genration ====================================================== */
/* ========================================================================= */

/* ========================================================================= */
/* ==== Drawing ============================================================ */

function cw_drawScreen() {
  ctx.clearRect(0,0,canvas.width,canvas.height);
  ctx.save();
  cw_setCameraPosition();
  ctx.translate(200-(camera_x*zoom), 200+(camera_y*zoom));
  ctx.scale(zoom, -zoom);
  cw_drawFloor();
  ghost_draw_frame(ctx, ghost);
  cw_drawCars();
  ctx.restore();
}

function cw_minimapCamera(x, y) {
  minimapcamera.left = Math.round((2+camera_x) * minimapscale) + "px";
  minimapcamera.top = Math.round((31-camera_y) * minimapscale) + "px";
}

function cw_setCameraTarget(k) {
  camera_target = k;
}

function cw_setCameraPosition() {
  if(camera_target >= 0) {
    var cameraTargetPosition = cw_carArray[camera_target].getPosition();
  } else {
    var cameraTargetPosition = leaderPosition;
  }
  var diff_y = camera_y - cameraTargetPosition.y;
  var diff_x = camera_x - cameraTargetPosition.x;
  camera_y -= cameraspeed * diff_y;
  camera_x -= cameraspeed * diff_x;
  cw_minimapCamera(camera_x, camera_y);
}

function cw_drawGhostReplay() {
  carPosition = ghost_get_position(ghost);
  camera_x = carPosition.x;
  camera_y = carPosition.y;
  cw_minimapCamera(camera_x, camera_y);
  showDistance(Math.round(carPosition.x*100)/100, Math.round(carPosition.y*100)/100);
  ctx.clearRect(0,0,canvas.width,canvas.height);
  ctx.save();
  ctx.translate(200-(carPosition.x*zoom), 200+(carPosition.y*zoom));
  ctx.scale(zoom, -zoom);
  ghost_draw_frame(ctx, ghost);
  ghost_move_frame(ghost);
  cw_drawFloor();
  ctx.restore();
}


function cw_drawCars() {
  for(var k = (cw_carArray.length-1); k >= 0; k--) {
    myCar = cw_carArray[k];
    if(!myCar.alive) {
      continue;
    }
    myCarPos = myCar.getPosition();

    if(myCarPos.x < (camera_x - 5)) {
      // too far behind, don't draw
      continue;
    }

    ctx.strokeStyle = "#444";
    ctx.lineWidth = 1/zoom;

    for (var i = 0; i < myCar.wheels.length; i++){
      b = myCar.wheels[i];
      for (f = b.GetFixtureList(); f; f = f.m_next) {
        var s = f.GetShape();
        var color = Math.round(255 - (255 * (f.m_density - wheelMinDensity)) / wheelMaxDensity).toString();
        var rgbcolor = "rgb("+color+","+color+","+color+")";
        cw_drawCircle(b, s.m_p, s.m_radius, b.m_sweep.a, rgbcolor);
      }
    }
    
    var densitycolor = Math.round(100 - (70 * ((myCar.car_def.chassis_density - chassisMinDensity) / chassisMaxDensity))).toString() + "%";
    if(myCar.is_elite) {
      ctx.strokeStyle = "#44c";
      //ctx.fillStyle = "#ddf";
      ctx.fillStyle = "hsl(240,50%,"+densitycolor+")";
    } else {
      ctx.strokeStyle = "#c44";
      //ctx.fillStyle = "#fdd";
      ctx.fillStyle = "hsl(0,50%,"+densitycolor+")";
    }
    ctx.beginPath();
    var b = myCar.chassis;
    for (f = b.GetFixtureList(); f; f = f.m_next) {
      var s = f.GetShape();
      cw_drawVirtualPoly(b, s.m_vertices, s.m_vertexCount);
    }
    ctx.fill();
    ctx.stroke();
  }
}

function toggleDisplay() {
  if(cw_paused) {
    return;
  }
  canvas.width = canvas.width;
  if(doDraw) {
    doDraw = false;
    cw_stopSimulation();
    cw_runningInterval = setInterval(function() {
      var time = performance.now() + (1000 / screenfps);
      while (time > performance.now()) {
        simulationStep();
      }
    }, 1);
  } else {
    doDraw = true;
    clearInterval(cw_runningInterval);
    cw_startSimulation();
  }
}

function cw_drawVirtualPoly(body, vtx, n_vtx) {
  // set strokestyle and fillstyle before call
  // call beginPath before call

  var p0 = body.GetWorldPoint(vtx[0]);
  ctx.moveTo(p0.x, p0.y);
  for (var i = 1; i < n_vtx; i++) {
    p = body.GetWorldPoint(vtx[i]);
    ctx.lineTo(p.x, p.y);
  }
  ctx.lineTo(p0.x, p0.y);
}

function cw_drawPoly(body, vtx, n_vtx) {
  // set strokestyle and fillstyle before call
  ctx.beginPath();

  var p0 = body.GetWorldPoint(vtx[0]);
  ctx.moveTo(p0.x, p0.y);
  for (var i = 1; i < n_vtx; i++) {
    p = body.GetWorldPoint(vtx[i]);
    ctx.lineTo(p.x, p.y);
  }
  ctx.lineTo(p0.x, p0.y);

  ctx.fill();
  ctx.stroke();
}

function cw_drawCircle(body, center, radius, angle, color) {
  var p = body.GetWorldPoint(center);
  ctx.fillStyle = color;

  ctx.beginPath();
  ctx.arc(p.x, p.y, radius, 0, 2*Math.PI, true);

  ctx.moveTo(p.x, p.y);
  ctx.lineTo(p.x + radius*Math.cos(angle), p.y + radius*Math.sin(angle));

  ctx.fill();
  ctx.stroke();
}

function cw_drawMiniMap() {
  var last_tile = null;
  var tile_position = new b2Vec2(-5,0);
  minimapfogdistance = 0;
  fogdistance.width = "800px";
  minimapcanvas.width = minimapcanvas.width;
  minimapctx.strokeStyle = "#000";
  minimapctx.beginPath();
  minimapctx.moveTo(0,35 * minimapscale);
  for(var k = 0; k < cw_floorTiles.length; k++) {
    last_tile = cw_floorTiles[k];
    last_fixture = last_tile.GetFixtureList();
    last_world_coords = last_tile.GetWorldPoint(last_fixture.GetShape().m_vertices[3]);
    tile_position = last_world_coords;
    minimapctx.lineTo((tile_position.x + 5) * minimapscale, (-tile_position.y + 35) * minimapscale);
  }
  minimapctx.stroke();
}

/* ==== END Drawing ======================================================== */
/* ========================================================================= */

function saveProgress() {
  localStorage.cw_savedGeneration = JSON.stringify(cw_carGeneration);
  localStorage.cw_genCounter = gen_counter;
  localStorage.cw_ghost = JSON.stringify(ghost);
  localStorage.cw_topScores = JSON.stringify(cw_topScores);
  localStorage.cw_floorSeed = floorseed;
}

function restoreProgress() {
  if(typeof localStorage.cw_savedGeneration == 'undefined' || localStorage.cw_savedGeneration == null) {
    alert("No saved progress found");
    return;
  }
  cw_stopSimulation();
  cw_carGeneration = JSON.parse(localStorage.cw_savedGeneration);
  gen_counter = localStorage.cw_genCounter;
  ghost = JSON.parse(localStorage.cw_ghost);
  cw_topScores = JSON.parse(localStorage.cw_topScores);
  floorseed = localStorage.cw_floorSeed;
  document.getElementById("newseed").value = floorseed;

  for (b = world.m_bodyList; b; b = b.m_next) {
    world.DestroyBody(b);
  }
  Math.seedrandom(floorseed);
  cw_createFloor();
  cw_drawMiniMap();
  Math.seedrandom();

  cw_materializeGeneration();
  cw_deadCars = 0;
  leaderPosition = new Object();
  leaderPosition.x = 0;
  leaderPosition.y = 0;
  document.getElementById("generation").innerHTML = "generation "+gen_counter;
  document.getElementById("cars").innerHTML = "";
  document.getElementById("population").innerHTML = "cars alive: "+generationSize;
  cw_startSimulation();
}

function simulationStep() {
  world.Step(1/box2dfps, 20, 20);
  ghost_move_frame(ghost);
  for(var k = 0; k < generationSize; k++) {
    if(!cw_carArray[k].alive) {
      continue;
    }
    ghost_add_replay_frame(cw_carArray[k].replay, cw_carArray[k]);
    cw_carArray[k].frames++;
    position = cw_carArray[k].getPosition();
    cw_carArray[k].minimapmarker.style.left = Math.round((position.x+5) * minimapscale) + "px";
    cw_carArray[k].healthBar.width = Math.round((cw_carArray[k].health/max_car_health)*100) + "%";
    cw_carArray[k].healthBarGene.innerHTML = printGeneId(cw_carArray[k].car_def.genome);
    if(cw_carArray[k].checkDeath()) {
      cw_carArray[k].kill();
      cw_deadCars++;
      document.getElementById("population").innerHTML = "cars alive: " + (generationSize-cw_deadCars);
      cw_carArray[k].minimapmarker.style.borderLeft = "1px solid #ccc";
      if(cw_deadCars >= generationSize) {
        cw_newRound();
      }
      if(leaderPosition.leader == k) {
        // leader is dead, find new leader
        cw_findLeader();
      }
      continue;
    }
    if(position.x > leaderPosition.x) {
      leaderPosition = position;
      leaderPosition.leader = k;
    }
  }
  showDistance(Math.round(leaderPosition.x*100)/100, Math.round(leaderPosition.y*100)/100);
}

function cw_findLeader() {
  var lead = 0;
  for(var k = 0; k < cw_carArray.length; k++) {
    if(!cw_carArray[k].alive) {
      continue;
    }
    position = cw_carArray[k].getPosition();
    if(position.x > lead) {
      leaderPosition = position;
      leaderPosition.leader = k;
    }
  }
}

function cw_newRound() {
  if (mutable_floor) {
    // GHOST DISABLED
    ghost = null;
    floorseed = btoa(Math.seedrandom());

    world = new b2World(gravity, doSleep);
    cw_createFloor();
    cw_drawMiniMap();
  } else {
    // RE-ENABLE GHOST
    ghost_reset_ghost(ghost);
  }

  cw_nextGeneration();
  camera_x = camera_y = 0;
  cw_setCameraTarget(-1);
}

function cw_startSimulation() {
  cw_runningInterval = setInterval(simulationStep, Math.round(1000/box2dfps));
  cw_drawInterval = setInterval(cw_drawScreen, Math.round(1000/screenfps));
}

function cw_stopSimulation() {
  clearInterval(cw_runningInterval);
  clearInterval(cw_drawInterval);
}

function cw_kill() {
  var avgspeed = (myCar.maxPosition / myCar.frames) * box2dfps;
  var position = myCar.maxPosition;
  var score = position + avgspeed;
  document.getElementById("cars").innerHTML += Math.round(position*100)/100 + "m + " +" "+Math.round(avgspeed*100)/100+" m/s = "+ Math.round(score*100)/100 +"pts<br />";
  ghost_compare_to_replay(replay, ghost, score);
  cw_carScores.push({ i:current_car_index, v:score, s: avgspeed, x:position, y:myCar.maxPositiony, y2:myCar.minPositiony });
  current_car_index++;
  cw_killCar();
  if(current_car_index >= generationSize) {
    cw_nextGeneration();
    current_car_index = 0;
  }
  myCar = cw_createNextCar();
  last_drawn_tile = 0;
}

function cw_resetPopulation() {
  document.getElementById("generation").innerHTML = "";
  document.getElementById("cars").innerHTML = "";
  document.getElementById("topscores").innerHTML = "";
  cw_clearGraphics();
  cw_carArray = new Array();		//Throw away the old cars
  cw_carGeneration = new Array();
  cw_carScores = new Array();
  cw_topScores = new Array();
  cw_graphTop = new Array();
  cw_graphElite = new Array();
  cw_graphAverage = new Array();
  geneId = 0;
  lastmax = 0;
  lastaverage = 0;
  lasteliteaverage = 0;
  swapPoint1 = 0;
  swapPoint2 = 0;
  cw_generationZero();
}

function cw_resetWorld() {
  doDraw = true;
  cw_stopSimulation();
  for (b = world.m_bodyList; b; b = b.m_next) {
    world.DestroyBody(b);
  }
  floorseed = document.getElementById("newseed").value;
  Math.seedrandom(floorseed);
  cw_createFloor();
  cw_drawMiniMap();
  Math.seedrandom();
  cw_resetPopulation();
  cw_startSimulation();
}

function cw_confirmResetWorld() {
  if(confirm('Really reset world?')) {
    cw_resetWorld();
  } else {
    return false;
  }
}

// ghost replay stuff

function cw_pauseSimulation() {
  cw_paused = true;
  clearInterval(cw_runningInterval);
  clearInterval(cw_drawInterval);
  old_last_drawn_tile = last_drawn_tile;
  last_drawn_tile = 0;
  ghost_pause(ghost);
}

function cw_resumeSimulation() {
  cw_paused = false;
  ghost_resume(ghost);
  last_drawn_tile = old_last_drawn_tile;
  cw_runningInterval = setInterval(simulationStep, Math.round(1000/box2dfps));
  cw_drawInterval = setInterval(cw_drawScreen, Math.round(1000/screenfps));
}

function cw_startGhostReplay() {
  if(!doDraw) {
    toggleDisplay();
  }
  cw_pauseSimulation();
  cw_ghostReplayInterval = setInterval(cw_drawGhostReplay,Math.round(1000/screenfps));
}

function cw_stopGhostReplay() {
  clearInterval(cw_ghostReplayInterval);
  cw_ghostReplayInterval = null;
  cw_findLeader();
  camera_x = leaderPosition.x;
  camera_y = leaderPosition.y;
  cw_resumeSimulation();
}

function cw_toggleGhostReplay(button) {
  if(cw_ghostReplayInterval == null) {
    cw_startGhostReplay();
    button.value = "Resume simulation";
  } else {
    cw_stopGhostReplay();
    button.value = "View top replay";
  }
}
// ghost replay stuff END

// initial stuff, only called once (hopefully)
function cw_init() {
  // clone silver dot and health bar
  var mmm  = document.getElementsByName('minimapmarker')[0];
  var hbar = document.getElementsByName('healthbar')[0];

  for(var k = 0; k < generationSize; k++) {

    // minimap markers
    var newbar = mmm.cloneNode(true);
    newbar.id = "bar"+k;
    newbar.style.paddingTop = k*9+"px";
    minimapholder.appendChild(newbar);

    // health bars
    var newhealth = hbar.cloneNode(true);
    newhealth.getElementsByTagName("DIV")[0].id = "health"+k;
    newhealth.car_index = k;
    document.getElementById("health").appendChild(newhealth);
  }
  mmm.parentNode.removeChild(mmm);
  hbar.parentNode.removeChild(hbar);
  floorseed = btoa(Math.seedrandom());
  world = new b2World(gravity, doSleep);
  cw_createFloor();
  cw_drawMiniMap();
  cw_generationZero();
  cw_runningInterval = setInterval(simulationStep, Math.round(1000/box2dfps));
  cw_drawInterval    = setInterval(cw_drawScreen,  Math.round(1000/screenfps));
}

function relMouseCoords(event){
    var totalOffsetX = 0;
    var totalOffsetY = 0;
    var canvasX = 0;
    var canvasY = 0;
    var currentElement = this;

    do{
        totalOffsetX += currentElement.offsetLeft - currentElement.scrollLeft;
        totalOffsetY += currentElement.offsetTop - currentElement.scrollTop;
    }
    while(currentElement = currentElement.offsetParent)

    canvasX = event.pageX - totalOffsetX;
    canvasY = event.pageY - totalOffsetY;

    return {x:canvasX, y:canvasY}
}

HTMLDivElement.prototype.relMouseCoords = relMouseCoords;

minimapholder.onclick = function(event){
  var coords = minimapholder.relMouseCoords(event);
  var closest = { 
    index: 0,
    dist: Math.abs(((cw_carArray[0].getPosition().x + 6) * minimapscale) - coords.x),
    x: cw_carArray[0].getPosition().x
  }
  
  var maxX = 0;
  for (var i = 0; i < cw_carArray.length; i++){
    if (!cw_carArray[i].alive){
      continue;
    }
    var pos = cw_carArray[i].getPosition();
    var dist = Math.abs(((pos.x + 6) * minimapscale) - coords.x);
    if (dist < closest.dist){
      closest.index = i;
      closest.dist = dist;
      closest.x = pos.x;
    }
    maxX = Math.max(pos.x, maxX);
  }
  
  if (closest.x == maxX){ // focus on leader again
    cw_setCameraTarget(-1);
  } else {
    cw_setCameraTarget(closest.index);
  }
}

cw_init();
