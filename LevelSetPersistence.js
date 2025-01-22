//
// Sublevel Persistence of a finite time series that includes arbitrary flats
//
// Georg Essl & Robin Belton(February 2024-January 2025)
//
// Thanks to Nicole Sanderson for seeding the idea and early discussions.
//
'use strict';


//
// General purpose utility
//

// Basic debug messages.
function print(a)
{
//  console.log(a);
}

// More critical debug messages.
function printc(a)
{
//  console.log(a);
}

// Convenince to type mod arithmetic for circular domains

Number.prototype.mod = function(n) {
  return ((this%n)+n)%n;
}

// Find the location of an element in an array (or the nearest before it)
function locationOf(element, array, start, end) {
  if(array.length==0) return 0;
  start = start || 0;
  end = end || array.length;
  var pivot = parseInt(start + (end - start) / 2, 10);
  if (array[pivot] === element) return pivot;
  if (end - start <= 1)
    return array[pivot] > element ? pivot - 1 : pivot;
  if (array[pivot] < element) {
    return locationOf(element, array, pivot, end);
  } else {
    return locationOf(element, array, start, pivot);
  }
}

// Insert an element into an array at the proper order position. We  use it to construct set of levels.
function insertOrdered(element, array) {
  let loc = locationOf(element, array);
  if(array[loc]!=element)
  {
    array.splice(loc + 1, 0, element);
  }
  return array;
}


// Get global min and max. Meant to be used on data arrays like dataY. This allows for inversion of function and using the dual maximum.
function getGlobalMinMax(arr) {
  let min = arr[0];
  let max = arr[0];

  for (let i = 1; i < arr.length; i++) {
    if (arr[i] < min) {
      min = arr[i];
    } else if (arr[i] > max) {
      max = arr[i];
    }
  }

  return [min, max];
}

//
// Structure classes for Merge Trees and Box Snakes
//




// Tree Data structure for Merge Trees.

class TreeNode {
  constructor(value,x,ntype) {
    this.y = value;             // Associated y value of the merge moment
    this.x = x;                 // x position of one of the merges of the node
    this.ntype = ntype;         // minimum or maximum
    this.parent= null;          // parent
    this.descendants = [];      // children
  }
  addChild(cld)
  {
    this.descendants.push(cld);
    cld.setParent(this); 
  }
  setParent(p)
  {
    this.parent = p;
  }
}

// Snake box rectangle

class Rectangle {
  constructor(dx,sx,sy,ex,ey,dir,ext, bar=null, barlink=null) {
    this.dx = dx;         // x width
    this.sx = sx;         // absolute start x position in data
    this.sy = sy;         // y corner value on the left.
    this.ex = ex;         // absolute end x position in data
    this.ey = ey;         // y corner value on the right.
    this.dir = dir;       // direction (-1,0,1) for min, const, max
    this.ext = ext;       // is extremum (true,false)
    this.bar = bar;       // associated bar (unused)
    this.barlink = barlink;    // link to bar structure (unused)
  }
  clone() {
    return new Rectangle(this.dx, this.sx, this.sy,this.ex,this.ey,this.dir,this.ext,this.bar,this.barlink);
  }
}

//let this.boxsnake = [];

class LSP { // Export wrapper
  constructor() {
    this.computesuperlevelset = false;  // Compute sublevel or superlevelset? This uses the theorem in Belton & Essl and computes the superlevel set via inversion of then inversion of barcodes.
    this.computeboxsnakes = true;       // Disable computing box snakes

    this.mindirorder = -1;              // This specifies if we are going with a local min-first or max-first order.

    this.mergetree = null;              // Current MergeTree
    this.lastMaxNode = null; // GEORG GLOBAL AND LOCAL. CHECK

    this.betti1 = 0;                    // Do we have a cycle in H_1? Used for informational purposes
    this.usecircular = false;           // Domain is linear: false  Domain is circular: true

    this.boxsnake = [];                 // This is the global data structure for the box snake associated with the current dataY
    this.leftboxsnake = null;         // This is the left split box snake from and for surgery.
    this.rightboxsnake = null;        // This is the right split box snake from and for surgery

    this.noiseremove = false;           // Use true if noise rejection is active.
    this.noiselevel = 1e-12;            // Low noise floor to capture numerical inaccuracies only. Intended to deal with numerical noise from FFT.

    this.bars = 0;                      // Current bar count (used by barcode construction)
    this.barextrema = 0;                // Counts how many extrema have been used to construct a bar. 1 means it's incomplete. 0 means it's empty. 2 should never happen as it implies compete.
    this.lastbar = null;                // Keeps track of the last incomplete bar created
    this.barcode = [];                  // stored barcode of a dataset
    this.leftbarcode;                   // If split, left split barcode
    this.rightbarcode;                  //      ..., right split barcode

    this.showelder = false;             // Computer Elder Barcode (method decided by overridemergetreeelder)
    this.overridemergetreeelder = false;  // Computer Elder barcode from Merge Tree or via modified Barychikov's algorithm

    this.datasplit = false;             // Split state of data    

    this.basepoint = 0;                 // box snake rectangles can change base points under surgery. It's also a good way to check if surgery went right via integrity/unit tests.
    this.rightbasepoint = 0;            // box snake rectangles can change base points under surgery. It's also a good way to check if surgery went right via integrity/unit tests.

    this.dataY = null;                  // Current full data sequence
    this.isconstfunc = false;           // true if the data was found to be constant based on min and max matching. Fast const detection.
    this.globalmax = Number.NEGATIVE_INFINITY;              // Global maximum of the current data set
    this.globalmin = Number.POSITIVE_INFINITY;              // Global minimum of the current data set
    
    
    this.setoflevels = [];              // Stores the set of levels from data

    let nopert = true;                  // Perturb x-axis embedding: false   Use uniform embedding: true
    this.xpert = [];                    // X-axis perturbations to illustrate arbitrariness of embedding
  }

setData(data)
{
  this.dataY = data;
  const [gmin, gmax] = getGlobalMinMax(this.dataY);
  this.globalmax = gmax;                      // We need the global max to characterize bars that "end" at the total space (infinity bars in classical persistence). Invariant of static data so only needs to be computed when data changes (shifts for example)!
  this.globalmin = gmin;                      // Global min allows us to invert data and get the inverted max in O(1)
  this.isconstfunc = (gmin == gmax);          // Getting if a function is constant turns all computation on constant functions into O(1)
} 

// count how many consecutive samples from position p are "flat". This is a non-mod version hence does not work correctly for circular domains
countFlats(p)
{
  for(let i=p;i<this.dataY.length-1;i++)
  {
    if(this.dataY[i]!=this.dataY[i+1])
    {
      return i-p;
    }
  }

  return this.dataY.length-p;
}

// Generates barcode from box snake rectangles. This compute a local bar code construction rule (minimum to nearest unoccupied maximum, which is starting left due to boundary but flips at the global maximum to arrive at right at the other boundary) for both circular and linear domains
// Input(s):  rectangles[] .. box snake structure
//            mindirorder  .. compute superlevel or sublevel set by reversing roles of minima and maxima
//            usecircular  .. box snakes are for circular domain
// Output: barcode[] .. barcodes using a local barcode rule

getBarcodefromRectangles(rectangles)
{
  this.barcode = [];
  this.bars = 0;
  this.barextrema = 0;
  let firstmax = -1;
//  let this.globalmax = this.globalmax;
  let havetotalbar = false;
  print("GETTING BARS FROM RECTANGLES "+rectangles.length+" GLOBALMAX at "+this.globalmax);

  if(rectangles.length==1) // Must be a constant flat, can be computed in O(1)
  {
    if(this.usecircular==true)
      this.betti1=1; // One cycle for periodic constant data
    else
      this.betti1=0; // Linear order domain with boundaries
    // No editable content because all zeroes is unique persistence profile
    this.constructBar(rectangles[0].sx, rectangles[0].ex, rectangles[0].sy,-1);
    this.constructBar(rectangles[0].sx, rectangles[0].ex, rectangles[0].ey,1);
    return this.barcode;
  }

  for(let i=0;i<rectangles.length;i++)                  // Computational complexity O(n) where n is the number of box snakes which is no larger than the number of samples.
  {
    if(i<rectangles.length && rectangles[i].ext==false) // Skipping a possible monotone (we can start with a monotone in the circular case)
    {
      i++;
    }
    if(i>=rectangles.length)                            // Was the last box a monotone (should only happen in the circular case)? We are done!
    {
      break; // We are done with the loop
    }
    if(rectangles[i].ext==true && rectangles[i].dir==this.mindirorder)
    {
      print("Min found "+i);
      this.constructBar(rectangles[i].sx,rectangles[i].ex, rectangles[i].sy,this.mindirorder);    // Fill in the minima of a bar
      i++;
      if(i<rectangles.length && rectangles[i].ext==false) // Skipping a possible monotone
      {
        i++;
      }
      if(i>=rectangles.length) // Did we exhaust all rectangles? Done!
      {
        break; // We are done with the loop
      }
      if(i<rectangles.length-1 || this.usecircular == true) // Exclude border maxima. They do not contribute to homology
      {
        print("max found "+i);
        this.constructBar(rectangles[i].sx,rectangles[i].ex, rectangles[i].sy,-this.mindirorder);    // Fill in the maximum of a bar
      }
      if(this.usecircular == false && rectangles[i].sy == this.globalmax && havetotalbar == false)   // In the linear case a global extremum flips local orientation of the bar code construction rule due to one of the two merged connected components characterizing the total space ("infinity" bar).
      {
        this.constructBar(rectangles[i].sx,rectangles[i].ex, rectangles[i].sy,-this.mindirorder);    // Fill in the maximum of a bar
        havetotalbar = true;        // We have assigned a bar to capture the total space ("bar to infinity" in classical persistence). This happens when the global maximum is in the boundary.
      }
    }
    else
      firstmax = i;
  }

  if(this.usecircular == false)
  {
    print("complete");
    this.completeBars(-this.mindirorder); // Complete incomplete bar (if needed). This should only happen if the left boundary is a minimum.
  }
  else if (firstmax != -1)                           // Did we skip a first max? In the circular case that completes the circle!
  {
    this.constructBar(rectangles[firstmax].sx,rectangles[firstmax].ex, rectangles[firstmax].sy,-this.mindirorder);
  }
  return this.barcode;
}

// Shift Data to the left. Amount is given by the size of newDataY, which is the data to be shifted in.
// Input:  newDataY    array of data to be shifted in. Should be shiftlength long.
// Modifies: newData   surgically removed shiftlength worth of data and appends newDataY, surgically correcting snake boxes.
shiftDataLeft(newDataY)
{
  if(this.computeboxsnakes==false) return;

  print("LEFTSHIFT "+this.usecircular);
  let wascircular = this.usecircular;        // If domain is circular we will have to fix that after the shift surgery is completed.
  if(this.usecircular==true)
  {
    this.splitBoxes(this.dataY.length-1); // Decircularize
  }

  this.splitBoxes(newDataY.length-1); // Split Discardable piece in front
  this.dataY.splice(0,newDataY.length);         // Remove the old data from the array
  let oldDataY = this.dataY;
  this.dataY = newDataY;
  this.computeSnakeBoxes();

  this.fixRectPoints(this.rightboxsnake,0);           // These fix absolute positions into data inside snake boxes. Could be improved by using relative positioning only in snake boxes, and one global index
  this.fixRectPoints(this.boxsnake,oldDataY.length);
  this.dataY = [ ...oldDataY, ...newDataY];        // Merge sample data with shifted in data

  this.leftboxsnake = this.boxsnake;
  this.boxsnake = this.mergeBoxes(this.rightboxsnake,this.leftboxsnake);    // Compute merge surgery for snake boxes

  if(wascircular==true)
  {
    this.boxsnake = this.mergeBoxes(this.boxsnake,this.boxsnake);
  }
//  mergeTreefromSnakeBox();  // These are disabled for streaming performance.
//  computeBarcode();         // These are disabled for streaming performance.
//  barcode = getBarcodefromRectangles(rectangles);  // Alternative
}

// Shift Data to the right. Amount is given by the size of newDataY, which is the data to be shifted in.
// Input:  newDataY    array of data to be shifted in. Should be shiftlength long.
// Modifies: newData   surgically removed shiftlength worth of data and appends newDataY, surgically correcting snake boxes.
//
shiftDataRight(newDataY)
{
  if(this.computeboxsnakes==false) return;

  print("RIGHTSHIFT "+this.usecircular);
  let wascircular = this.usecircular;
  if(this.usecircular==true)
  {
    this.splitBoxes(this.dataY.length-1); // Decircularize
  }
  this.splitBoxes(this.dataY.length-newDataY.length-1); // Split Discardable piece in back

  for(let i=0;i<newDataY.length;i++)
    this.dataY.pop();
  let oldDataY = dataY;
  dataY = newDataY;
  this.computeSnakeBoxes();

  // Indices are naturally correct for surgery in this case as both newDataY and oldDataY start at 0, so no need to fix absolute references into data positions.

  dataY = [ ...newDataY, ...oldDataY ];
  this.rightboxsnake = this.boxsnake;
  this.boxsnake = this.mergeBoxes(this.rightboxsnake,this.leftboxsnake);
  if(wascircular==true)
  {
    this.boxsnake = this.mergeBoxes(this.boxsnake,this.boxsnake);
  }

  this.mergeTreefromSnakeBox();
  computeBarcode();
//  barcode = getBarcodefromRectangles(rectangles); // Alternative
  shiftcnt = shiftcnt + 1;
}

// Utility to debug print the merge tree (unused)

printMergeTree(node)
{
  if(node)
  {
    print(node.x+" "+node.y);
    for(let i=0; i<node.descendants.length; i++)
    {
      printMergeTree(node.descendants[i]);
    }
  }
}

//
// Flat skip functions. These are crucial to allow flats processing.
//

// skip flat sample region wrapper that uses either denoised or strict versions
skipFlatsMod(s,p)
{
  if(this.noiseremove==true)
    return skipFlatsModNoise(s,p);
  else
    return this.skipFlatsModStrict(s,p);
}

// skip flat sample region, with a noise tolerance. Recommended is to use this just above numerical inaccuracies to get rid of arithmetically induced noise.
// Compare Essl DAFx24.  
// We use noiselevel=1e-12;             // Low noise floor to capture numerical inaccuracies only. Intended to deal with numerical noise from FFT.

skipFlatsModNoise(s,p)
{
  for(let i=s;i<p+s;i++)
  {
    if(abs(this.dataY[i.mod(p)]-this.dataY[(i+1).mod(p)])>noiselevel)
      {
        return i+1;
      }
  }
  return s+p;
}

// skip flat sample regions, strict. Uses modulo arithmetic hence works on circular domains. In linear use check if it overflowed.
skipFlatsModStrict(s,p)
{
  for(let i=s;i<p+s;i++)
  {
    if(this.dataY[i.mod(p)]!=this.dataY[(i+1).mod(p)])
      {
        return i+1;
      }
  }
  return s+p;
}

// skip to the left instead of to the right
leftskipFlatsModStrict(s,p)
{
  for(let i=s;i>s-p;i--)
  {
    if(this.dataY[i.mod(p)]!=this.dataY[(i-1).mod(p)])
      {
        if(i!=s) print("lefskipped"+(i-1)+" "+s);
        return i-1;
      }
  }
  return s+p;
}

//
// Compute the box snake structure from an array of samples, also has bar code computation embedded using local bar code rules.
// Input:  dataY        .. array of samples
// Output: Rectangles   .. box snake structure array
//         barcode      .. array of bars

computeSnakeBoxes()
{
  if(this.computeboxsnakes == false) return;
  let direction = 0;
  let startflat = 0;
  let periodstart = 0;
  let p = this.dataY.length;
  let startmonotone = 0;
  let startmonotonedata = 0;
  let i=0;
//  let this.globalmax = this.globalmax;
  let havetotalbar = false;
  print("computeSnakeBoxes GLOBALMAX at "+this.globalmax);
  
  this.barextrema = 0;
  this.boxsnake = [];
  this.barcode = [];
  this.bars = 0;
  let currentbar = -1; // No bar if negative

  this.betti1 = 0; // We presume nonconstant signal

  startflat = i;
  i = this.skipFlatsMod(i,p);
  
  if(i == startflat+p) // is constant. Technically we know this from isconstfunc but this is here in case it is useful. Can be used as a "unit test" for constancy.
  {
    if(this.usecircular==true)
      this.betti1=1; // One cycle for periodic constant data
    else
      this.betti1=0; // Linear order domain with boundaries
    // No editable content because all zeroes is unique persistence profile
    this.constructBar(0, p-1, this.dataY[0],-1);
    currentbar = this.constructBar(0, p-1, this.dataY[p-1],1);
    this.boxsnake.push(
      new Rectangle(p,0,this.dataY[0],p-1,this.dataY[p-1],0,true,currentbar,this.lastbar)); // Extremum without direction  == constant
    this.basepoint = 0;
    return;
  }

  let firstflat = i;
  direction = Math.sign(this.dataY[i]-this.dataY[i-1]);
  while((this.dataY[i]-this.dataY[i-1])*direction >= 0)
  {
    startflat = i;
    i = this.skipFlatsMod(i,p);
  }  
  
  periodstart = i;

  if(this.usecircular==false)
    {
      if(direction==1) // Is a minimum, then allow a bar to be constructed.
      currentbar = this.constructBar(0, firstflat-1, this.dataY[0],-direction);
      this.boxsnake.push(new Rectangle(firstflat,0,this.dataY[0],firstflat-1,this.dataY[(firstflat-1).mod(p)],-direction,true,currentbar,this.lastbar)); // Boundary extremum
      this.basepoint = 0;
      if(startflat>firstflat) //
      {
        this.boxsnake.push(new Rectangle(startflat-firstflat,firstflat,this.dataY[(firstflat-1).mod(p)],startflat-1,this.dataY[(startflat).mod(p)],direction,false,currentbar,this.lastbar)); // First monotone
      }
    }
  else
  {
    this.basepoint = startflat;
    print("BASE POINT for Circular: "+this.basepoint);
  }

  while(i<p+periodstart)
  {
    {
      currentbar = this.constructBar(startflat, i-1, this.dataY[(i-1).mod(p)],direction);
      this.boxsnake.push(new Rectangle(i-startflat,startflat,this.dataY[startflat.mod(p)],i-1,this.dataY[(i-1).mod(p)],direction,true,currentbar));
      if(this.dataY[(i-1).mod(p)]==this.globalmax && this.usecircular==false && havetotalbar == false)
        {
          currentbar = this.constructBar(startflat, i-1, this.dataY[(i-1).mod(p)],direction); // Pushing second max as first global connects two components. This forces a direction switch of barcodes.
          havetotalbar = true;          // We have assigned a bar to capture the total space ("bar to infinity" in classical persistence). This happens when the global maximum is in the boundary.          
        }

        direction = -direction; // New monotone direction
    }

    if(this.usecircular == false && i>=this.dataY.length)
    {
      this.completeBars(direction); // Complete incomplete bar.
      return;
    }

    // Monotone Ascend next    
    startmonotone = i;
    startmonotonedata = this.dataY[(i-1).mod(p)];
    while ((this.dataY[(i).mod(p)]-this.dataY[(i-1).mod(p)])*direction >= 0) // Follow monotone section
    {
          startflat = i;
          i = this.skipFlatsMod(i,p);
          if(this.usecircular == false && i>=this.dataY.length)
            {
              if(startmonotone<startflat) // A residual monotone before boundary extremum
                this.boxsnake.push(new Rectangle(startflat-startmonotone,startmonotone,this.dataY[(startmonotone-1).mod(p)],startflat-1,this.dataY[(startflat).mod(p)],direction,false,currentbar,this.lastbar));
              currentbar = this.constructBar(startflat, this.dataY.length-1, this.dataY[(this.dataY.length-1).mod(p)],direction);
              this.completeBars(-direction); // Complete incomplete bar.
              this.boxsnake.push(new Rectangle(this.dataY.length-startflat,startflat,this.dataY[(startflat).mod(p)],this.dataY.length-1,this.dataY[(this.dataY.length-1).mod(p)],direction,true,currentbar,this.lastbar)); // Boundary extremum
              return;
            }
    }

    if(startmonotone < startflat){// && startmonotonedata!=this.dataY[(i-1).mod(p)]){ // Found any samples inbetween extrema
      this.boxsnake.push(new Rectangle(startflat-startmonotone,startmonotone,this.dataY[(startmonotone-1).mod(p)],startflat-1,this.dataY[(startflat).mod(p)],direction,false,currentbar,this.lastbar));

//      constructBar(startmonotone, startflat-1, this.dataY[(startflat).mod(p)],direction);
    }   
  }
    
  print("R");
  print(this.boxsnake);   
  print(this.barcode);
  return;
}

// Compute Persistent Homology via variations of Barychnikov's algorithm
//
// computePH_circular is the circularized case
// computePH_n is the altered version to handle boundaries without Barychnikov's assumptions.
// computePH_orig essentially Barychnikov's algorithm with minor variations in implementation.

computePH()
{
  if(this.usecircular==true)
    computePH_circular();
  else
    computePH_n();
//    computePH_orig();
}


// Partially constructs a bar from an extremum.
// It either starts an incomplete bar if this.barextrema is zero
// Or it completes an incomplete bar if this.barextrema is one.
// barcode[bar][0] is the minimum
// barcode[bar][1] is the maximum
// Code expects that it's called either min->max or max->min
// dir is the type of extremum. -1 is minimum 1 is maximum
constructBar(s,i,data,dir)
{
//  print("bb: "+s+" "+i+" d:"+(dir+1)/2+"("+dir+") "+bars+" "+data);
  if(this.barextrema==0)
  {
    this.barcode[this.bars]=[];
    this.lastbar = this.barcode[this.bars];
  }
  this.barcode[this.bars][(dir+1)/2]=[s,i,data];
  this.barextrema = this.barextrema+1;
  if(this.barextrema>1)
    {
      this.bars = this.bars+1;
      this.barextrema = 0;
      return this.bars-1; // Return just completed bar
    }
    return this.bars; // Return bar in construction
}

// Completes an incomplete bar, by connecting it to the global maximum.
// dir is the direction of the missing part.
completeBars(dir)
{
  if(this.barextrema == 1)
  {
    console.log("completing "+this.barextrema+" "+this.globalmax);
//    let this.globalmax = this.globalmax;
    this.barcode[this.bars][(dir+1)/2] = [this.dataY.length-1,this.dataY.length-1,this.globalmax];
    this.barextrema = 0;
    this.bars = this.bars+1;
    return this.bars;
  }
}

// Compute Persistent Homology using a circularized modified version of the Barychnikov algorithm.
computePH_circular()
{
  let minbuffer = new Array();
  let maxbuffer = new Array();
  let startflat = 0;
  let periodstart = 0;
  let maxmaxindex = 0;
  let minminindex = 0;
  let maxmax = -190;
  let minmin = 190;
  let p = this.dataY.length;
  this.barcode = [];
  let i=0;
  let direction = 0;
  
  print("COMPUTEPH_CIRCULAR");
  startflat = i;
  i = this.skipFlatsMod(i,p);

  
  if(i == startflat+p) // is constant. Technically we know this from isconstfunc but this is here in case it is useful. Can be used as a "unit test" for constancy.
  {
    this.betti1=1; // One cycle for periodic constant data
    // No editable content because all zeroes is unique persistence profile
    this.barcode.push([[0,p,this.dataY[0]],this.dataY[0]]);
    return;
  }    
    
  direction = Math.sign(this.dataY[i]-this.dataY[i-1]);

  while((this.dataY[i]-this.dataY[i-1])*direction >= 0)
  {
    startflat = i;
    i = this.skipFlatsMod(i,p);
  }  
  
  periodstart = i;

  while(i<p+periodstart)
  {
    if(direction == 1)
    {
      maxbuffer.push([startflat,i-startflat,this.dataY[(i-1).mod(p)]]);
      if(this.dataY[i]>maxmax)
      {
          maxmaxindex = i;
          maxmax = this.dataY[i];
      }
    }
    else
    {
      minbuffer.push([startflat,i-startflat,this.dataY[(i-1).mod(p)]]);
      if(this.dataY[i]<minmin)
        {
          minminindex = i;
          minmin = this.dataY[i];
        }
    }

    direction = -direction; // New monotone direction

    while ((this.dataY[(i).mod(p)]-this.dataY[(i-1).mod(p)])*direction >= 0) // Follow monotone section
    {
      startflat = i;
      i = this.skipFlatsMod(i,p);
    }
  }   
  let bars = maxbuffer.length;

  for(let i=0;i<bars;i++)
  {
      this.barcode.push([minbuffer[i.mod(bars)],maxbuffer[i.mod(bars)]]);
  }
}

// Modifier version of Barychnikov's algorithm
// See Essl DAFx24. Comments relate to symbolic algorithm in the paper.
computePH_n()
{
  
// Maxima, Minima ← empty stacks ▷ Initializing
  let maxstack = new Array(); // Stack
  let minstack = new Array(); // Stack
  let startflat = 0;
  this.barcode = [];
  let maxmaxentry = [0,0,-maxmax];
  let p = this.dataY.length;
  let i=0;
  let cmaxmax = -180;
  let cminmin = 180;

  print("COMPUTEPH_N");
  startflat = i;
  i = this.skipFlatsMod(i,p);

  
  if(i == startflat+p)
  {
//    betti1=1; // One cycle for periodic constant data
    // No editable content because all zeroes is unique persistence profile
    this.barcode.push([[0,p,this.dataY[0]],maxmaxentry]);
    return;
  }    

// Direction ← +1 
  let direction = Math.sign(this.dataY[i]-this.dataY[i-1]);

  let periodstart = i;
// for t = 1, . . . , N d
  while(i<periodstart+p)
  {
//if (f(t) − f(t − 1)) × Direction < 0 then ▷ Direction changes, so either
//if Direction = +1 then
//Maxima.Push((t − 1, f(t − 1)) ▷ add the local maximum
//else
//Minima.Push((t − 1, f(t − 1)) ▷ ...or minimum to respective stack,
//end if
    startflat = i;
    i = this.skipFlatsMod(i,p);

//      print(this.dataY[i]-this.dataY[i-1]*direction+" "+this.dataY[i]+" "+this.dataY[i-1]+" "+direction);
    if((this.dataY[i.mod(p)]-this.dataY[(i-1).mod(p)])*direction < 0)
    {
      if(direction == +1)
      {
        print("max "+startflat+" "+(i-startflat)+" "+this.dataY[i-1]);
        maxstack.push([startflat,i-startflat,this.dataY[(i-1).mod(p)]]);
        if (this.dataY[(i-1).mod(p)] > cmaxmax) cmaxmax = this.dataY[(i-1).mod(p)];
        if (this.dataY[(i-1).mod(p)] == this.globalmax && minstack.length > 0 && this.usecircular == false) // We found our global, so we found our elder.
        {
          console.log("ELDER found");
          this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
          minstack.pop();
          maxstack.pop();
        }
      }
      else
      {
        print("min "+startflat+" "+(i-startflat)+" "+this.dataY[i-1]);
      minstack.push([startflat,i-startflat,this.dataY[(i-1).mod(p)]]);
      if (this.dataY[(i-1).mod(p)] < cminmin) cminmin = this.dataY[(i-1).mod(p)];
      } 
//      Direction = −Direction ▷ and record change of the direction.
      direction = -direction;
    }
    else
    {
      if(direction == -1 && minstack.length > 0 && this.dataY[(i-1).mod(p)]<minstack[minstack.length-1][2])
      {
        this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
        
        minstack.pop();
        maxstack.pop();
      }

      // If stored max data is smaller than the current ascending slope we can create a barcode as it is the shorter of the currently considered level sets.
      if(direction == 1 && maxstack.length > 0 && this.dataY[(i-1).mod(p)]>maxstack[maxstack.length-1][2])
      {
//      print("+: "+minstack[minstack.length-1]+" "+maxstack[maxstack.length-1]);

        this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
        
        minstack.pop();
        maxstack.pop();
      }
    }
//end if
//end if
//end for
  }
  //  print("bars: "+bars+" "+barcode.length);
  let bars = maxstack.length;
//  print("bars: "+bars+" "+barcode.length);
  for(let i=0;i<bars;i++)
  {
      this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
      minstack.pop();
      maxstack.pop();
  }
  if(minstack.length>0) // Connect remaining minimum to the global maximum
  {
    console.log("Completing");
    this.completeBars(1);
  }
}

// let firstmax;

localFromTree(tree,relx,dir)
{
  let xdist=Number.MAX_VALUE; // high minimum to seed. Our data goes from -180,180.
  let neighborbranch=null;
  let branch;
  let branchage;
  let minx;
  let minl;
  let minarray = [];
  let maxarray = [];
  let ominy;
  let ominx;
  let ominl;
  let starti;
  let endi;
  
  if(tree.descendants==null || tree.descendants.length == 0)
    {
      return [tree, tree.y, tree.x, 1];
    }
  
  if(dir==-1)
  {
//    return neighborDescent(tree.descendants[0],relx,dir);
  }

  for(let i=0; i<tree.descendants.length;i++)
    {
      [branch,branchage,minx,minl] = localFromTree(tree.descendants[i],relx,dir);
      
      if((dir == -1 && i !=0) || (dir==1 && i!=tree.descendants.length-1))
        {
          
          //make barcode for all the deaths
          this.barcode.push([[minx,minl,branchage],[tree.x,1,tree.y]]);
          print("bcmt2: "+this.barcode[this.barcode.length-1]+". "+branchage+" "+minx+" "+minl);
        }
      else
        {
          print("elsed "+branchage+" "+minx+" "+minl+" "+dir);
          ominy = branchage;
          ominx = minx;
          ominl = minl;
        }
    }
  return [tree, ominy, ominx, ominl];
}

// Barcode rule is neighbor. Tribal council rule is neighbor.
localBarcodefromMergeTree()
{
  let neighborbranch=null;
  this.barcode = [];
  let branchage;
  let minx;
  let minl;
  let dir = 1;
  print("LOCALBCFROMTREE");
  
  for(let i=0;i<this.mergetree.descendants.length;i++) 
    {
      if(i>0) dir = -1;
      [neighborbranch, branchage, minx,minl] = localFromTree(this.mergetree.descendants[i],this.mergetree.x,dir);
      this.barcode.push([[minx,minl,branchage],[this.mergetree.x,1,this.mergetree.y]]);
//      print("bcmt: "+barcode[barcode.length-1]);
    }
  
//  print("MTBCL "+barcode.length);
}

// Recusrive call for generating barcode vis elder rule from a merge tree.

elderFromTree(tree)
{
  let elderly=Number.MAX_VALUE; // high minimum to seed. Our data goes from -180,180.
  let elderbranch=null;
  let branch;
  let branchage;
  let minx;
  let minl;
  let minarray = [];
  let ominx;
  let ominl;
  
  if(tree.descendants==null || tree.descendants.length == 0)
    {
      return [tree, tree.y, tree.x, 1];
    }
  
  for(let i=0; i<tree.descendants.length;i++)
    {
      [branch, branchage, minx,minl] = elderFromTree(tree.descendants[i]);
      minarray.push([minx,minl,branchage]);
      
//      print("BA "+branchage);
      if(branchage < elderly)
        {
          elderbranch = branch; 
          elderly = branchage;
        }
    }
  
//  print(elderly);
  for(let i=0; i<tree.descendants.length;i++)
    {
      [minx,minl,branchage] = minarray[i];
      
      if(tree.descendants[i] != elderbranch)
        {
          //make barcode for all the deaths
          this.barcode.push([[minx,minl,branchage],[tree.x,1,tree.y]]);
//          print("bcmt2: "+barcode[barcode.length-1]+". "+branchage+" "+minx+" "+minl);
        }
      else
        {
//          print("elsed "+branchage+" "+minx+" "+minl)
          ominx = minx;
          ominl = minl;
        }
    }
  return [tree, elderly, ominx, ominl];
}

// Barcode rule is traditional elder. Tribal council rule is left-most elder.
elderBarcodefromMergeTree()
{
  if(this.computeboxsnakes==false) return;   // All our merge trees are derived from box snakes. If this changes this check should be removed.
//  localBarcodefromMergeTree();
//  return;
  
  let elderbranch=null;
  this.barcode = [];
  let branchage;
  let minx;
  let minl;

  print("ELDERBCFROMTREE");
  
  for(let i=0;i<this.mergetree.descendants.length;i++) 
    {
      [elderbranch, branchage, minx,minl] = elderFromTree(this.mergetree.descendants[i]);
      this.barcode.push([[minx,minl,branchage],[this.mergetree.x,1,this.globalmax]]); // This is the elder so it needs to go to this.globalmax
//      print("bcmt: "+barcode[barcode.length-1]);
    }
  
//  print("MTBCE "+barcode.length);
}

// Create Merge Tree from box snake
// Input:  rectangles[]  .. box snake structure
// Output: mergetree  .. merge tree structure

mergeTreefromSnakeBox()
{
  if(this.computeboxsnakes==false) return;
  let lastmin = null;
  let lastmax = null;
  let maxstack = [];
  let lastmaxnode = null;
  let leftmaxnode = null;
  let newmax = null;
  let tempx = null;
  let tempxmin = null;
  print("MERGETREESTART "+this.boxsnake.length);

  if(this.boxsnake.length==1) // Constant data, which is both a minimum and a maximum and has a point-height barcode
  {
    tempx = (this.boxsnake[0].ex+this.boxsnake[0].sx)/2;
    this.mergetree = new TreeNode(this.boxsnake[0].sy,tempx,1);
    this.mergetree.addChild(new TreeNode(this.boxsnake[0].sy, tempx, -1));
    return;
  }
  
  for(let i=0;i<this.boxsnake.length; i++)
  {
    if(this.boxsnake[i].ext!=false) // is an extremum
    {
      if(this.boxsnake[i].dir==1 && lastmin != null && (i != this.boxsnake.length-1 || this.usecircular == true)) // New Maximum?
      {
        if(lastmax == null)                                                 // First maximum?
        {
          lastmax = this.boxsnake[i].sy;
          tempx = (this.boxsnake[i].ex+this.boxsnake[i].sx)/2;
//                  tempx = rectangles[i].sx;
          lastmaxnode =  new TreeNode(lastmax,tempx,1);
          lastmaxnode.addChild(new TreeNode(lastmin, tempxmin, -1));
          leftmaxnode = lastmaxnode;
          maxstack.push(lastmaxnode);
//                  print("push0 "+maxstack.length);
          lastmin = null;
        }
        else
        {
          if(lastmax == this.boxsnake[i].sy)
          {
            tempx = (this.boxsnake[i].ex+this.boxsnake[i].sx)/2;
//                    tempx = rectangles[i].sx;
            lastmaxnode.addChild(new TreeNode(lastmin,tempxmin, -1));
            lastmin = null;
          }
          else if(lastmax > this.boxsnake[i].sy)
          {
            lastmax = this.boxsnake[i].sy;
            tempx = (this.boxsnake[i].ex+this.boxsnake[i].sx)/2;
//                      tempx = rectangles[i].sx;
            newmax = new TreeNode(this.boxsnake[i].sy,tempx,1);
            newmax.addChild(new TreeNode(lastmin,tempxmin,-1));
            lastmin = null;
//                      maxstack[maxstack.length-1].addChild(newmax);
            leftmaxnode = newmax;
            maxstack.push(newmax);
//                      print("push1 "+maxstack.length+"  "+rectangles[i].sx+" "+rectangles[i].sy);
          }
          else // lastmax < rectangles[i].sy
          {
            lastmaxnode = maxstack.pop();//maxstack[maxstack.length-1];
            lastmaxnode.addChild(new TreeNode(lastmin,tempxmin, -1));
            lastmin = null;
            lastmax = lastmaxnode.y;
//                      print("pop "+maxstack.length+"  "+rectangles[i].sx+" "+rectangles[i].sy);
            
            while(maxstack.length>0 && maxstack[maxstack.length-1].y < this.boxsnake[i].sy) // Stacked max is parent
            {
              newmax = maxstack.pop();
              newmax.addChild(lastmaxnode);
              lastmaxnode = newmax;
              lastmax = lastmaxnode.y;
//                          print("pop2 "+maxstack.length);
            }
            
            if(maxstack[maxstack.length-1] == this.boxsnake[i].sy) // Merge
            {
              // no nothing
            }
            else // Stored max is biggest, so new node is separate subtree
            {
              lastmax = this.boxsnake[i].sy;
              tempx = (this.boxsnake[i].ex+this.boxsnake[i].sx)/2;
              newmax = new TreeNode(lastmax,tempx,1);
              newmax.addChild(lastmaxnode);
              maxstack.push(newmax);
//                          print("push3 "+maxstack.length+" "+rectangles[i].sx+" "+rectangles[i].sy);
              lastmaxnode = newmax;
              lastmax = lastmaxnode.y;
            }
          }
        }
      }
      if(this.boxsnake[i].dir==-1)
      {
        lastmin = this.boxsnake[i].sy;
        tempxmin = (this.boxsnake[i].ex+this.boxsnake[i].sx)/2;
        if(i == this.boxsnake.length-1)
        {
/*                  if(newmax==null)
            newmax = lastmaxnode;
//                  newmax.addChild(new TreeNode(lastmin,tempxmin, -1));
//                  lastmin=null;
*/
        }
//            tempxmin = rectangles[i].sx;
      }
    }
  }
  
  if(lastmin!=null)
  {
    print("maxstack "+maxstack.length);
    if(maxstack.length>0)
    {
      newmax = maxstack.pop();
      newmax.addChild(new TreeNode(lastmin,tempxmin, -1));
//          print("pop4 "+lastmin+" "+tempxmin);
      while(maxstack.length>0)
      {
        maxstack[maxstack.length-1].addChild(newmax);
        newmax = maxstack.pop();
      }
      lastmaxnode = newmax;
    }
    else // This happens when all maxima are in the boundary. They become homologically active by merging with an existing minimum that only "merged" into the total set at the maximum
      // This is an interesting case because technically this is a non-unique situation. Both left and right boundary maxima connect to the minima in this case, if the minimum at question is not in the boundary.
    {
      let i;
      if(this.boxsnake[0].dir==1) // Left boundary is maximum.
      {
        i=0;
      }
      else if(this.boxsnake[this.boxsnake.length-1].dir==1) // Right boundary is maximum.
      {
        i=this.boxsnake.length-1;
      }
      else
      {
        // THIS SHOULD NEVER HAPPEN!
      }
      lastmax = this.boxsnake[i].sy;
//            tempx = (rectangles[i].ex+rectangles[i].sx)/2;
//                  tempx = rectangles[i].sx;
      lastmaxnode =  new TreeNode(lastmax,tempxmin,1); // We place the X at the minimum because it's the original connected component. Technically this is an essential tree branch.
      lastmaxnode.addChild(new TreeNode(lastmin,tempxmin, -1));
    }
  }
  
//  print("MERGETREE");
  this.mergetree = lastmaxnode;
//  if(overridemergetreeelder==true)
//    elderBarcodefromMergeTree();
//  printMergeTree(lastmaxnode);
//  plotfullMergeTree(lastmaxnode);
}

// Picks a method to compute the barcode based on selection and conditions.

computeBarcode()
{
  print("COMPUTEBARCODE csls="+this.computesuperlevelset)
  if(this.computesuperlevelset)
    invertData();
  
  this.computeSnakeBoxes();
  this.mergeTreefromSnakeBox();

  if(this.overridemergetreeelder==true)
    {
      elderBarcodefromMergeTree();
    }
  else if(this.showelder)
    computePH();
//    computePH_orig_s();
  else if(this.datasplit==true)
  {
    this.leftbarcode = this.getBarcodefromRectangles(this.leftboxsnake);
    this.rightbarcode = this.getBarcodefromRectangles(this.rightboxsnake);
  }
  else
    {
//        mergeTreefromSnakeBox();
//        computeBarcode();
    this.barcode = this.getBarcodefromRectangles(this.boxsnake);
    }
  
  if(this.computesuperlevelset)
  {
    invertData();
    invertBarcode();
//    computeSnakeBoxes();
  }
  if(this.computesuperlevelset)
    print("super "+this.barcodemode);
  else
    print("sub "+this.barcodemode);
}

// Wrapper that allows us to more easily select between Barychnikov variants.

computePH_orig_s()
{
//    computePH_orig();
    computePH_n();    // Use our modified version
}

// Compute sublevel set persistence with flats.
// This is an extension of an algorithm given by Barychnikov to compute persistent homology of time series data with a few extensions.
// He assumed a global "-infinity" minimum to the left and a global "infinity" maximum to the right providing a specific anchor to the barcode construction that wasn't suitable for us.
// His case does not handle circular cases, we realize the circular case in computePH_circular()
// This is essentially an implementation of the original algorithm without the needed modifications. The linear case can be found in computePH_n()
computePH_orig() {
  // Uses Barychnikov's stack based bar data construction.
  let maxstack = new Array(); // Stack
  let minstack = new Array(); // Stack
  this.barcode = [];

  print("computePH_orig");
  
  let direction = 0;
  let startflat = 0;
  let flatlen = 0;
  let maxmax = -190;
  let minmin = 190;
  let maxmaxentry = [0,0,maxmax];
  let minminentry = [0,0,minmin];
  let monotonestart = 0;

  for(let i=0; i<this.dataY.length-1;i++)
  {
    // Keep track of global minima and maxima. Global minimum is not explicitly used but could be used to verify correctness of the elder bar (it needs to go from global minimum to global maximum). Global maximum is used if the last maximum is the global maximum, and then enters the elder bar. This is up to elder representation convention as we want it to be finite to make much of any sense.
    if(this.dataY[i]<minmin) minmin = this.dataY[i];
    // First (flat) sample maximum is excluded because it cannot contribute to homology.
    if(i!=0 && this.dataY[i]>maxmax) {maxmax = this.dataY[i]; maxmaxentry = [startflat,flatlen,this.dataY[i]];}
    
    startflat = i;
    flatlen = countFlats(i);
    i=i+flatlen;

    switch(direction)
    {
      case 0: // Flat start
        if((this.dataY[i+1]-this.dataY[i]) > 0)
        {
          direction = 1; // Ascending Start -> Min
          minstack.push([startflat,flatlen,this.dataY[i]]);
        }
        else if((this.dataY[i+1]-this.dataY[i]) < 0)
        {
          direction = -1; // Descending Start -> Max
          
          monotonestart = i+1;
        }
        break;
      case 1: // Found Max
        if((this.dataY[i+1]-this.dataY[i]) < 0) // Found Max
        {
          direction = -1;
          maxstack.push([startflat,flatlen,this.dataY[i]]);
          monotonestart = i+1;
        }
        break;
      case -1: // Found Min
        if((this.dataY[i+1]-this.dataY[i]) > 0) // Found Max
        {
          direction = 1;
          minstack.push([startflat,flatlen,this.dataY[i]]);
          monotonestart = i+1;
        }
        break;
    }

    // If stored min data is larger than the current descending slope we can create a barcode as it is the shorter of the currently considered level sets.
    if(direction == -1 && minstack.length > 0 && this.dataY[i+1]<=minstack[minstack.length-1][2]){

      this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
      
      minstack.pop();
      maxstack.pop();
    }

    // If stored max data is smaller than the current ascending slope we can create a barcode as it is the shorter of the currently considered level sets.
    if(direction == 1 && maxstack.length > 0 && this.dataY[i+1]>=maxstack[maxstack.length-1][2]){

      this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
      
      minstack.pop();
      maxstack.pop();
    }
  }

  // Finished core loop.
  
  // Check if last sample is global minimum or maximum.
  if(this.dataY[this.dataY.length-1]<minmin) minmin = this.dataY[this.dataY.length-1];

  // Check if last sample is a minimum hence a generator of a connected component.  
    if(direction == -1 || direction == 0)
    {
      // A minimum at boundary creates a connected component, hence needs to be accounted for.
      minstack.push([startflat,flatlen,this.dataY[this.dataY.length-1]]);
    }
  
  // This exists for debugging purposes only and can be cut.
    if(direction == 1 || direction == 0)
    {
      // No contribution here as a boundary cannot join, and a max is not creating anew connected component
    }

  let bars = maxstack.length;
  for(let i=0;i<bars;i++)
  {
      this.barcode.push([minstack[minstack.length-1],maxstack[maxstack.length-1]]);
      minstack.pop();
      maxstack.pop();
  }
  
  // Create elder bar
  if(minstack.length>0 && this.mindirorder == -1)
  {
    this.barcode.push([minstack[0],maxmaxentry]); // Outstanding Elder Barcode
  }
  else if(maxstack.length>0 && this.mindirorder == 1)
  {
    this.barcode.push([minstack[0],minminentry]); // Outstanding Elder Barcode
  }
}

//
// find a box snake rectangle based on x coordinate position. This is used as building block to allow interactively deforming box snakes.
//

findbox(x)
{
  for(let i=0;i<this.boxsnake.length;i++)
    {
  let sxm = this.boxsnake[i].sx.mod(this.dataY.length);
  let exm = this.boxsnake[i].ex.mod(this.dataY.length);

      if(sxm<=exm) // No folding over
        {
        if(sxm-0.5<x && exm+0.5>x)
          {
            return i;
          }
        }
      else // Handle the fold
        {
          if(sxm-0.5<x && this.dataY.length+0.5>x)
            {
              return i;
            }
          if(0<= x && x < exm+0.5)
            {
              return i;
            }
        }
    }
    return -1; // No rectangle.
}



// find the snake box which contains an x coordinate in the data
// Input(s):    x .. x coordinate
//              p .. length of the data (for modulus)
//              b .. base point in case data was shifted
// Output(s):   i .. index of found rectangle.
//              boxdy .. y of the data at x     (before the surgery split)
//              boxdyp1 .. y of the data at x+1 (after the surgery split)

findboxbyindex(x,p,b)
{
  let csx = b;
  let boxdx;
  let boxdy;
  let boxdyp1;
if(this.boxsnake[0].sx != b) print("BASEPOINT OFF!"+this.boxsnake[0].sx+" "+b);
  for(let i=0;i<this.boxsnake.length;i++)
    {
//      print(`${rectangles[i].sx} ${x} ${rectangles[i].ex}`)
      boxdx = this.boxsnake[i].dx;
      if((((csx)<=x) && (((csx+boxdx-1))>=x)) || (((csx+p)<=x+p) && ((csx+boxdx-1+p)>=x+p)))
      {
        boxdy = this.dataY[x%p];
        boxdyp1 = this.dataY[(csx+boxdx+p)%p];
        print("BEX "+boxdy+" "+boxdyp1);
        return [i,boxdy, boxdyp1];
      }
      csx = csx+boxdx;
    }
  print("No rectangle found! "+x+" "+this.boxsnake.length);
  return [-1,0,0];
}

// Fixes absolute positions into data potentially changed by surgery.
// O(n). This could be optimized by making box snakes relative to some base points and not use absolute positions.
// We use them for clarity of implementation at O(n) cost.
fixRectPoints(rect,x)
{
  if(x==0)
  {
    this.fixRectBase(rect);
    return;
  }
  let s = rect[0].sx;
  for(let i=0; i<rect.length;i++)
  {
    rect[i].sx = rect[i].sx-s+x;
    rect[i].ex = rect[i].ex-s+x;
  }
}

fixRectBase(rect)
{
  let sx=0;
  for(let i=0; i<rect.length;i++)
  {
    let dx = rect[i].dx;
    rect[i].sx = sx;
    rect[i].ex = sx+dx-1;
    sx = sx + dx;
  }
}

//
// Surgery of Box Snakes
//

// Merge to box snake arrays via local surgery moves.
// Input(s):  leftboxsnake  .. left rectangle to merge 
//            rightboxsnake .. right rectangle to merge if same array as left, it's a circular merge
// Output:    rectangles      .. box snake array for merged (or circularized) data
mergeBoxes(leftboxsnake, rightboxsnake)
{
  let mergecircular = leftboxsnake==rightboxsnake;
  if(mergecircular == true)
    this.usecircular = true;

  // E-E Merge: Different extremum 1-1 length boxes
  // Single rectangles imply constant. So this is two constants that are glued at different levels, convering them to extrema relative to each other.
  if(leftboxsnake.length == 1 && rightboxsnake.length == 1 && leftboxsnake[leftboxsnake.length-1].ey != rightboxsnake[0].sy)
  {
    print("E-E Merge (diff 1-1)");
    // Fix dir and ext data
    let dir = Math.sign(leftboxsnake[0].sy-rightboxsnake[0].sy);        // Compute the direction between the glued levels.
    leftboxsnake[0].dir=dir;                                              // convert from constant to the correct extrema
    rightboxsnake[0].dir=-dir;                                            // extrema are necessarily opposite to each other.
    leftboxsnake[0].ext=true;                                             // This should be true, but it's fixed on principle.
    rightboxsnake[0].ext=true;
    this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);    // Fix the x positions to be correct for the merged case
    if(mergecircular == false)
    {
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];                // non-circular, just concatenate the fixed box snake structures
    }
    else this.boxsnake = leftboxsnake;                                       // circular, both are the same but now with fixed box snake structure.
    this.integritycheck(this.basepoint,this.boxsnake);  // test structure for issues, disable this for performance.
    return this.boxsnake;
  }
  // E-E Merge: Same extremum, merge into one
  // Two extrema of the same type are merged. This implies that they can simply be combined into one snake box.
  // This also includes the cast of a constant being merged at the same level with either another constant, or an extremum at that level.
  else if(leftboxsnake[leftboxsnake.length-1].ey == rightboxsnake[0].sy && (leftboxsnake[leftboxsnake.length-1].dir == rightboxsnake[0].dir || leftboxsnake[leftboxsnake.length-1].dir==0 || rightboxsnake[0].dir==0))
  {
    print("E-E Merge (same)");

    if(leftboxsnake == rightboxsnake && leftboxsnake.length==1)  // Is it a constant merged into a circle?
    {
      print("E-E Merge (circular)");
      this.boxsnake = leftboxsnake;                // We are done!
      return this.boxsnake;
    }

    // Adjust the rightmost box of the left box snake structure to absorb the leftmost box on the right.
    leftboxsnake[leftboxsnake.length-1].ex=
        leftboxsnake[leftboxsnake.length-1].ex+rightboxsnake[0].dx;// was+rightboxsnake[0].ex-rightboxsnake[0].sx+1;
    leftboxsnake[leftboxsnake.length-1].dx = leftboxsnake[leftboxsnake.length-1].ex - leftboxsnake[leftboxsnake.length-1].sx + 1;

    if(leftboxsnake[leftboxsnake.length-1].dir !=rightboxsnake[0].dir)    // Is one side a constant? dir is 0 for a constant.
    {
      print("Merged in constant: "+leftboxsnake[leftboxsnake.length-1].dir+" "+rightboxsnake[0].dir);
      let dir = leftboxsnake[leftboxsnake.length-1].dir + rightboxsnake[0].dir; // One is zero so this just gets is the direction, if both are zero it's a merged constant!
      leftboxsnake[leftboxsnake.length-1].dir = dir;
      rightboxsnake[0].dir = dir;
    }
    if(rightboxsnake.length>1) // Is there more than one rectangle on the right side to merge? If yes, we have to remove the one we integrated on the left and keep the rest.
    {
      print("squash");
      rightboxsnake.shift(); // Get rid of one extremum
    }
    if(rightboxsnake.length>0 && mergecircular == false)          // If there is something left to the right, fix it's x positions for the merge.
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
    else
      this.basepoint = leftboxsnake[0].sx;
    print(`B ${leftboxsnake.length} ${rightboxsnake.length}`);
    if(mergecircular == false)
    {
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];        // Noncircular: Merge the two and we are done.
    }
    else
    {
      this.boxsnake = leftboxsnake;                                  // Circular: return the left.
      print("Recircularize complete "+leftboxsnake.length+" "+rightboxsnake.length);
    }

    this.integritycheck(this.basepoint,this.boxsnake);
    return this.boxsnake;
  }
  else if(leftboxsnake.length >=2 && rightboxsnake[0].dir == 0) // Non-const left, Constant right
  {
    print("*-C Merge");
    // Merge circular should always be false for this case. There is no constant possible
    let dir = -Math.sign(leftboxsnake[leftboxsnake.length-1].ey-rightboxsnake[0].sy);
    if(dir == 0) // The constant is merged at level of border extremum on the left. Simply absorb the constant into the border.
    {
      print("FlatE-C Merge");
      // Just grow the extremum flat
      leftrectanges[leftboxsnake.length-1].ex = leftrectanges[leftboxsnake.length-1].ex+1;
      leftrectanges[leftboxsnake.length-1].dx = leftrectanges[leftboxsnake.length-1].dx+1;
      // Discard right as it's now merged
      this.boxsnake = leftboxsnake;
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
    else if(dir == leftboxsnake[leftboxsnake.length-1].dir) // Dir agree -> right becomes new border extremum, left extremum is a monotone, possibly fusing with an existing one.
    {
      print("Monotone-C Merge ");
      rightboxsnake[0].dir = dir;
      // Merge Left Monotone
      leftboxsnake[leftboxsnake.length-1].ext = false;      // Convert left to monotone
      let tex = leftboxsnake[leftboxsnake.length-1].ex;
      if(leftboxsnake[leftboxsnake.length-2].ext == false)  // Are we next to an existing monotone?
        {
          print("full monotone");
          leftboxsnake.pop();                                 // Yes? Get rid the boundary one as we will fuse into one monotone.
        }
        else
          leftboxsnake[leftboxsnake.length-1].sy=leftboxsnake[leftboxsnake.length-2].ey; // Align monotone with leftmost extremum

      leftboxsnake[leftboxsnake.length-1].ex=tex;           // Fix the end of the fused monotone (if needed)          
      leftboxsnake[leftboxsnake.length-1].dx=leftboxsnake[leftboxsnake.length-1].ex-leftboxsnake[leftboxsnake.length-1].sx+1;  // fix the length of the box
      leftboxsnake[leftboxsnake.length-1].ey=rightboxsnake[0].sy;               // align box height with new extremum on the right.
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);    // fix absolute positions
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];                          // Merge. Notice that this cannot be a circular merge as both sides would have to be constant!
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
    else // dir disagrees, meaning the constant simply becomes an opposite extremum.
    {
      print("*-E-C (diff) Merge"+rightboxsnake[0].dir+" "+dir);
      rightboxsnake[0].dir = dir;
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);    // Make sure that that one new extremum has the right absolute positions.
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];                          // Merge! Again cannot be circular.
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
  }
  else if(rightboxsnake.length >=2 && leftboxsnake[leftboxsnake.length-1].dir == 0)  // Left is a constant. Same deal as above just with reversed roles.
  {
    print("C-* Merge");
    // Merge circular should always be false for this case. There is no constant possible
    let dir = -Math.sign(leftboxsnake[leftboxsnake.length-1].ey-rightboxsnake[0].sy);
    if(dir == 0) // Flat extremum
    {
      print("C-FlatE Merge");
      // Just grow the extremum flat
      rightboxsnake[0].ex = rightboxsnake[0].sx-1;
      rightboxsnake[0].dx = rightboxsnake[0].ex-rightboxsnake[0].sx+1;
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
      // Discard left as it's now merged
      this.boxsnake = rightboxsnake;
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
    else if(dir == -rightboxsnake[0].dir) // Dir agree -> Merge left into Monotone
    {
      print("C-Monotone Merge");
      leftboxsnake[leftboxsnake.length-1].dir = -dir;
      // Merge Left Monotone
      rightboxsnake[0].ext = false;
      rightboxsnake[0].dir = dir;
      let tsx = rightboxsnake[0].sx;
      if(rightboxsnake[1].ext == false)
        {
          print("full monotone");
          rightboxsnake.shift();
        }
        else
          rightboxsnake[0].ey=rightboxsnake[1].sy; // Align monotone with leftmost extremum

      rightboxsnake[0].sx=tsx;
      rightboxsnake[0].dx=rightboxsnake[0].ex-rightboxsnake[0].sx+1;
      rightboxsnake[0].sy=leftboxsnake[leftboxsnake.length-1].ey;
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
    else // dir disagrees
    {
      print("C-E-* (diff) Merge");
      leftboxsnake[leftboxsnake.length-1].dir = -dir;
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
  }
  // E-E Merge (diff): Opposite extrema, where the gradient in the merge indicates that they remain extrema.
  else if(rightboxsnake[0].dir != 0 && leftboxsnake[leftboxsnake.length-1].dir !=0 && leftboxsnake[leftboxsnake.length-1].ey != rightboxsnake[0].sy && leftboxsnake[leftboxsnake.length-1].dir != rightboxsnake[0].dir && (Math.sign(rightboxsnake[0].sy-leftboxsnake[leftboxsnake.length-1].ey)==rightboxsnake[0].dir )) 
  {
    print("E-E Merge (diff)");
    // Opposing Extrema that match their gradient. Just merge.
    if(mergecircular == false)
    {
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
    }
    else this.boxsnake = leftboxsnake;
    this.integritycheck(this.basepoint,this.boxsnake);
    return this.boxsnake;
  }
  else if(leftboxsnake.length >=2)             // Left box snake has space for a monotone to extremal merge? Check for that case.
  {
    // M-E Merge (one side looks monotone and non extremal after merge)
    // l-1 == monotone(d) or ext(-d)
    // l == ext(d)
    // r == ext(d)
    let dir;
    if(leftboxsnake[leftboxsnake.length-2].ext == false)          // Is there an existing monotone near the boundary?
      dir = leftboxsnake[leftboxsnake.length-2].dir;              // get its direction
    else
      dir = -leftboxsnake[leftboxsnake.length-2].dir;             // If it's an extremum get the direction a minotone would have if the boundary was to become one.

    if(leftboxsnake[leftboxsnake.length-1].ext == true &&
      leftboxsnake[leftboxsnake.length-1].dir == dir &&
      rightboxsnake[0].ext == true &&
      ((rightboxsnake[0].dir == dir &&
      dir*leftboxsnake[leftboxsnake.length-1].sy < dir*rightboxsnake[0].ey) ||
      rightboxsnake[0].dir == 0)                                  // Right side extremum is in the right direction to turn the left boundary into a monotone
    )
    {
      print(`M-E Merge ${dir} ${leftboxsnake[leftboxsnake.length-2].ext} ${leftboxsnake[leftboxsnake.length-1].ext} ${rightboxsnake[0].ext}`);
      leftboxsnake[leftboxsnake.length-1].ext = false;          // left boundary no longer an extremum.
      let tex = leftboxsnake[leftboxsnake.length-1].ex;
      if(leftboxsnake[leftboxsnake.length-2].ext == false)      // Does it need to be fused with a neighboring monotone?
      {
        leftboxsnake.pop();                                     // Yes!
      }
      else
        leftboxsnake[leftboxsnake.length-1].sy=leftboxsnake[leftboxsnake.length-2].ey; // Align monotone with leftmost extremum

      leftboxsnake[leftboxsnake.length-1].ex=tex;             // Absorb fused monotone
      leftboxsnake[leftboxsnake.length-1].dx=leftboxsnake[leftboxsnake.length-1].ex-leftboxsnake[leftboxsnake.length-1].sx+1;
      leftboxsnake[leftboxsnake.length-1].ey=rightboxsnake[0].sy;
      leftboxsnake[leftboxsnake.length-1].dir = dir;          // Fix monotone direction
      if(rightboxsnake[0].dir == 0)                             // If right was constant, turn it into an extremum of the correct direction
      {
        rightboxsnake[0].dir = -Math.sign(tex-rightboxsnake[0].sy);
        print("fixdir "+rightboxsnake[0].dir+"" +tex+" "+rightboxsnake[0].sy);
      }
      if(mergecircular == false)
      {
        this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
        this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
      }
      else
      {
        this.boxsnake = leftboxsnake;
        print("Recircularize complete");
      }
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
  }
  if(rightboxsnake.length >=2)          // Right box snake has space for a monotone to extremal merge? Check for that case.
  {
    // E-M Merge (one side looks monotone and non extremal after merge)
    // l = ext(-d)
    // r = ext(-d)
    // r+1 == monotone(d) or ext(d)
    let dir;
    // Both cases are the same. This if is for elucidation compared to M-E(!)
    if(rightboxsnake[1].ext == false) // This if could be removed for optimization. It's here for symmetry with the E-M case where the orientations change.
      dir = -rightboxsnake[1].dir;
    else
      dir = -rightboxsnake[1].dir;
    
    if(rightboxsnake[0].ext == true &&
        rightboxsnake[0].dir == dir &&
        leftboxsnake[leftboxsnake.length-1].ext == true &&
        (leftboxsnake[leftboxsnake.length-1].dir == dir && dir*leftboxsnake[leftboxsnake.length-1].sy > dir*rightboxsnake[0].ey) || leftboxsnake[leftboxsnake.length-1].dir==0) 
    {
      print("E-M Merge "+leftboxsnake.length+" "+rightboxsnake.length);
      rightboxsnake[0].ext = false;
      let tex = rightboxsnake[0].sx;
      let tsy = rightboxsnake[1].ey;
      if(rightboxsnake[1].ext == false)
      {
        print("Remove Monotone");
        rightboxsnake.shift();
      }
      rightboxsnake[0].sx=tex;
      rightboxsnake[0].dx=rightboxsnake[0].ex-rightboxsnake[0].sx+1;
      rightboxsnake[0].sy=leftboxsnake[leftboxsnake.length-1].ey;
      rightboxsnake[0].ey=tsy;
      rightboxsnake[0].dir = -dir;
      if(mergecircular == false)
      {
        this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
        this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
        print("EM Out: "+this.boxsnake.length);
      }
      else
      {
        this.boxsnake = leftboxsnake;
        print("Recircularize complete "+this.boxsnake.length);
      }
      this.fixRectPoints(this.boxsnake,0);
      this.basepoint = this.boxsnake[0].sx;
      this.integritycheck(this.basepoint,this.boxsnake);
      return this.boxsnake;
    }
  }
  // Final case is an M-M merge. All other possibility have been taken care off so by process of elimination we know.
  {
    print("M-M Merge");
    // M-M Merge (both sides look monotone and non extremal after merge)
    // MON Merge l-1 <= l <= r <= r+1
    // l-1 == monotone(d) or ext(-d)
    // l == d
    // r == -d
    // r+1 == monotone(d) or ext(d)
    let tex = leftboxsnake[leftboxsnake.length-1].ex;
    leftboxsnake[leftboxsnake.length-1].ext=false;
    if(leftboxsnake[leftboxsnake.length-2].ext==false)        // If next to a monotone on the left fuse them and ditch one.
      leftboxsnake.pop();

    let tsx = rightboxsnake[0].sx;
    if(rightboxsnake[1].ext==false)                             // If next to a monotone on the right fuse them and ditch one.
      rightboxsnake.shift();

      rightboxsnake[0].sx = tsx;
    rightboxsnake[0].dx = rightboxsnake[0].ex-rightboxsnake[0].sx+1;
    let td = rightboxsnake[0].ex-rightboxsnake[0].sx+1;
    let tey = rightboxsnake[1].sy;
    rightboxsnake.shift();                                      // Get rid of one monotone, as the left and the right now are fused.
    leftboxsnake[leftboxsnake.length-1].ex=tex+td;            // Fix up all the rectangles to accomodate all the fused monotones.
    leftboxsnake[leftboxsnake.length-1].dx=leftboxsnake[leftboxsnake.length-1].ex-leftboxsnake[leftboxsnake.length-1].sx+1;
    print(leftboxsnake[leftboxsnake.length-1].sx+" "+leftboxsnake[leftboxsnake.length-1].ex+" "+leftboxsnake[leftboxsnake.length-1].dx);
    leftboxsnake[leftboxsnake.length-1].ey=tey;
    leftboxsnake[leftboxsnake.length-1].sy=leftboxsnake[leftboxsnake.length-2].ey;
    if(rightboxsnake.length>0 && mergecircular == false)        // Fix the absolute positions if needed.
      this.fixRectPoints(rightboxsnake,leftboxsnake[leftboxsnake.length-1].ex+1);
    print(`${leftboxsnake.length} ${rightboxsnake.length}`);
    if(mergecircular == false)
    {
      this.boxsnake = [...leftboxsnake, ...rightboxsnake ];
    }
    else
    {
      this.boxsnake = leftboxsnake;
      print("Recircularize complete "+leftboxsnake.length+" "+rightboxsnake.length);
    }
    this.basepoint = this.boxsnake[0].sx;
    this.integritycheck(this.basepoint,this.boxsnake);
    return this.boxsnake;
  }
}


// Split box snake structure
// Input(s):  rectangles  .. box snake structure
//            x           .. data position left of which to split the structure.
// Output(s): leftboxsnake  .. Left split snake box (if was not circular)
//            rightboxsnake .. Right split snake box  (if was not circular)
//            rectangles      .. Decircularized snake box (if was circular)
splitBoxes(x)
{

  let [i,boxdy,boxdyp1] = this.findboxbyindex(x,this.dataY.length,this.basepoint);          // Find the box affected by the surgery. It is either the left of two, or inside an affected rectangle.

  print("boxindex: "+i+" "+this.boxsnake.length+" "+this.basepoint);
//  fixBarOrigin(rectangles);
  
let lsplitrect;
let rsplitrect;

  if(this.boxsnake.length==1) // Decircularize a flat constant
  {
    // Splitting a single rectangle implies it must be a flat constant.
    if(this.usecircular == true)    // In the circular case it decircularizes into a linear sequence
    {
      print("Const Split (circular)");
      this.boxsnake[0].sx=x+1;
      this.boxsnake[0].ex=this.dataY.length+x;
      this.usecircular = false;
      this.basepoint = x+1;
    }
    else // In the linear case it split it into two separate constants
    {
      print("Const Split (linear) ");
      this.leftboxsnake = [];
      this.leftboxsnake[0]=this.boxsnake[0].clone();
      this.leftboxsnake[0].dx = x+1;
      this.leftboxsnake[0].sx = 0;
      this.leftboxsnake[0].ex = x;
      this.rightboxsnake = [];
      this.rightboxsnake[0]=this.boxsnake[0].clone();
      this.rightboxsnake[0].dx = this.dataY.length-x-1;
      this.rightboxsnake[0].sx = x+1;
      this.rightboxsnake[0].ex = this.dataY.length-1;
      print("CS "+this.leftboxsnake[0].dx+" "+this.rightboxsnake[0].dx+" "+this.dataY.length);
      this.integritycheck(this.rightboxsnake[0].sx,this.rightboxsnake,false);
      this.integritycheck(this.leftboxsnake[0].sx,this.leftboxsnake,false);
      this.rightbasepoint = this.rightboxsnake[0].sx;
    }
    return;
  }

  print("RX "+i+" "+this.boxsnake[i].ex+" "+x+" "+this.dataY.length+" "+this.boxsnake[i].ext);

  if(this.boxsnake[i].ex%this.dataY.length == x%this.dataY.length) // If the left split is the right end of a rectangle, so we need to consider two rectangles.  
  {
    print(`Boundary: ${i} ${i+1} ${this.boxsnake.length}`);
    if(this.boxsnake[i].ext==true && this.boxsnake[(i+1)%this.boxsnake.length].ext==true) // Both borders are already extrema!
    {
      // Split and do nothing!
      print("E-E Split "+(i+1));
      if(i+1<this.boxsnake.length)    // Are we cutting at the end of rectangles? This is only possible if folded over, usually due tocircularity.
      {
        this.leftboxsnake = this.boxsnake.slice(0, i+1);                 // No? Normal separation
        this.rightboxsnake = this.boxsnake.slice(i+1,this.boxsnake.length);
      }
      else
      {
        this.leftboxsnake = this.boxsnake.slice(i+1,this.boxsnake.length);  // Yes? Folded separation
        this.rightboxsnake = this.boxsnake.slice(0,i+1);
      }

      this.rightbasepoint = this.rightboxsnake[0].sx;
      if(this.rightboxsnake.length == 1 && this.usecircular == false)     // Did the right split become a singleton? If yes it must now be constant.
      {
        print("Fix");
        this.rightboxsnake[0].ext = true; // Must be flat constant
        this.rightboxsnake[0].dir = 0; // Must be flat constant
      }
      if(this.leftboxsnake.length == 1 && this.usecircular == false)      // Did the left split become a singleton? If yes it must now be constant.
      {
        print("Fix");
        this.leftboxsnake[0].ext = true; // Most be flat
        this.leftboxsnake[0].dir = 0; // Most be flat

      }
    }
    else // One of the rectangles is a monotone
    {
      if(this.boxsnake[i].ext == false) // First rect is a monotone
      {
        // The edge of a monotone became an extremum
        // Creates an asymmetry in extrema

        printc("M-E Split "+i+" "+this.boxsnake[0].sx+" "+this.boxsnake.length);
        if(i+1<this.boxsnake.length)                               // Are we cutting at the end of rectangles? This is only possible if folded over, usually due tocircularity.
        {
          this.leftboxsnake = this.boxsnake.slice(0, i);
          this.rightboxsnake = this.boxsnake.slice(i+1,this.boxsnake.length);
        }
        else
        {
          this.leftboxsnake = this.boxsnake.slice(i+1,this.boxsnake.length);
          this.rightboxsnake = this.boxsnake.slice(0,i);
        }
        if(this.boxsnake[i].sx==this.boxsnake[i].ex) // Just a single-length monotone block that needs to be converted to extremum
        {
          print("ME-Single!");
          this.boxsnake[i].ext=true;
          this.boxsnake[i].dir=this.boxsnake[i].dir;
          this.boxsnake[i].dx=1;
          this.boxsnake[i].sy=this.boxsnake[i].ey=boxdy;
          this.leftboxsnake.push(this.boxsnake[i]);
        }
        else               // Block is bigger than one sample? We need to chop it up.
        {
          lsplitrect = this.boxsnake[i%this.boxsnake.length].clone(); // Create a new box for the newly created left Extremum, we do this by cloning and modifying.
          let oldex = lsplitrect.ex;
          lsplitrect.ex = this.leftskipFlatsModStrict(lsplitrect.ex,this.dataY.length);    // Find the flat part, which becomes an extremum.
          lsplitrect.dx = lsplitrect.ex-lsplitrect.sx+1;
          print("dx "+lsplitrect.dx+" "+oldex+" "+lsplitrect.ex);
          lsplitrect.ey = this.dataY[(lsplitrect.ex+1)%this.dataY.length];

          rsplitrect = this.boxsnake[i].clone();                   // Create a new box for the newly created right Extremum

          rsplitrect.sx = lsplitrect.ex+1;
          rsplitrect.dx = rsplitrect.ex-rsplitrect.sx+1;
          rsplitrect.sy = rsplitrect.ey = this.dataY[rsplitrect.ex%this.dataY.length];
          rsplitrect.ext = true;

          print("!! "+(lsplitrect.ex-lsplitrect.sx)+" "+lsplitrect.ex+" "+lsplitrect.sx);
          if((lsplitrect.ex-lsplitrect.sx)>=0) // Monotone squashed? This can happen if the flat assigned to the extremum took all of the monotone. If not we keep the monotone.
          {
            this.leftboxsnake.push(lsplitrect);
          }
          this.leftboxsnake.push(rsplitrect);     // Definitely keep the newly created boundary extremum.
        }
        this.rightbasepoint = this.rightboxsnake[0].sx;
      }
      else // The second rectangle must be a monotone.
      {
        print("E-M Split "+(i+1)+" "+this.boxsnake.length);
        if(i+1<this.boxsnake.length)                          // More folding checks
        {
          this.leftboxsnake = this.boxsnake.slice(0, i+1);
          this.rightboxsnake = this.boxsnake.slice(i+2,this.boxsnake.length);
        }
        else
        {
          this.leftboxsnake = this.boxsnake.slice(i+2,this.boxsnake.length);
          this.rightboxsnake = this.boxsnake.slice(1,i+2);
        }
        print("EM2 "+this.rightboxsnake.length+" "+(i+1)+" "+(i+2));
        // This make left end of monotone an extremum
        // Creates one new extrema, essentially symmetric to the ME case above.
        if(this.boxsnake[(i+1)%this.boxsnake.length].sx==this.boxsnake[(i+1)%this.boxsnake.length].ex) // Just a single block that needs to be converted to extremum
        {
          print("EM-Single!");
          this.boxsnake[(i+1)%this.boxsnake.length].ext=true;
          this.boxsnake[(i+1)%this.boxsnake.length].dir=-this.boxsnake[(i+1)%this.boxsnake.length].dir;
          this.boxsnake[(i+1)%this.boxsnake.length].ey=this.boxsnake[(i+1)%this.boxsnake.length].sy=boxdyp1;

          this.rightboxsnake.unshift(this.boxsnake[(i+1)%this.boxsnake.length]);
        }
        else
        {
          lsplitrect = this.boxsnake[(i+1)%this.boxsnake.length].clone(); // Left Extremum
          lsplitrect.ex = this.skipFlatsMod(lsplitrect.sx,this.dataY.length)-1;
          lsplitrect.dx = lsplitrect.ex-lsplitrect.sx+1;
          lsplitrect.sy = lsplitrect.ey = this.dataY[lsplitrect.sx%this.dataY.length];
          lsplitrect.ext = true;
          lsplitrect.dir=-lsplitrect.dir;

          rsplitrect = this.boxsnake[(i+1)%this.boxsnake.length].clone(); // Left remaining monotone
          rsplitrect.sy = boxdyp1;// Was this.dataY[rsplitrect.sx%this.dataY.length];
          rsplitrect.sx = lsplitrect.ex+1;
          rsplitrect.dx = rsplitrect.ex-rsplitrect.sx+1;

          if((rsplitrect.ex-rsplitrect.sx)>=0) // Monotone squashed? No
          {
            print("No Mono Squish");
            this.rightboxsnake.unshift(rsplitrect);
          }
          this.rightboxsnake.unshift(lsplitrect);
          print("EM3 "+this.rightboxsnake.length+" "+this.leftboxsnake.length);
        }
        this.rightbasepoint = this.rightboxsnake[0].sx;
      }
    }
  }
  else  // Only case left is split inside a box snake. Could be inside an extremum flat, or inside a monotone.
  {
    // We know we can split everything aside from the affected box.
    this.leftboxsnake = this.boxsnake.slice(0, i);
    this.rightboxsnake = this.boxsnake.slice(i+1,this.boxsnake.length);
    // rectangle at x has not be treated
    print(`R(${i}): ${this.boxsnake.length} LR: ${this.leftboxsnake.length} RR: ${this.rightboxsnake.length}`);
    print(`${x} ${this.boxsnake[i].sx} ${this.boxsnake[i].ex}`);
    print(this.boxsnake[i].ext);
    if(this.boxsnake[i].ext==true) // Rectangle is an extremum
    {
      print("EXT SPLIT "+i);
      // This splits one existing extremum into two.
      lsplitrect = (this.boxsnake[i]).clone();
      lsplitrect.ex = x;
      lsplitrect.dx = lsplitrect.ex-lsplitrect.sx+1;
      rsplitrect = this.boxsnake[i].clone();
      rsplitrect.sx = x+1;
      rsplitrect.dx = rsplitrect.ex-rsplitrect.sx+1;
      this.leftboxsnake.push(lsplitrect);           // Add one split part to the left.
      this.rightboxsnake.unshift(rsplitrect);       // and the other to the right.
      if(this.rightboxsnake.length==1 && this.usecircular == false)   // right is length 1 -> Must be constant
      {
        this.rightboxsnake[0].dir = 0; // Must be flat
      }
      if(this.leftboxsnake.length==1 && this.usecircular == false)   // left is length 1 -> Must be constant
      {
        this.leftboxsnake[0].dir = 0; // Must be flat
      }
      this.rightbasepoint = this.rightboxsnake[0].sx;
    }
    else
    {
      print("MON SPLIT");
      let mlrect; // Monotone rect
      let mrrect; // Monotone rect
      let lexrect; // Left Extremum
      let rexrect; // Right Extremum

      // Splitting inside a monotone turns that one box into up to four. Minimum is 2 for boundary extrema.

      lexrect = this.boxsnake[i].clone(); // Left Extremum
      lexrect.ext = true;
      lexrect.dir = lexrect.dir;
      lexrect.sx = this.leftskipFlatsModStrict(x,this.dataY.length)+1;
      lexrect.ex = x;
      lexrect.dx = lexrect.ex - lexrect.sx+1;
      lexrect.sy = lexrect.ey = this.dataY[(x)%this.dataY.length];
      
      rexrect = this.boxsnake[i].clone(); // Right Extremum
      rexrect.dir = -rexrect.dir;
      rexrect.ext = true;
      rexrect.sx = (x+1)%this.dataY.length;
      rexrect.ex = (this.skipFlatsMod(rexrect.sx,this.dataY.length)-1)%this.dataY.length;
      rexrect.dx = rexrect.ex - rexrect.sx+1;
      rexrect.sy = rexrect.ey = this.dataY[(x+1)%this.dataY.length];

      mlrect = this.boxsnake[i].clone(); // Left Monotone rect
      mlrect.ex = lexrect.sx-1;
      mlrect.dx = mlrect.ex - mlrect.sx+1;
      mlrect.ey = this.dataY[(x)%this.dataY.length];

      mrrect = this.boxsnake[i].clone(); // Right Monotone rect
      mrrect.sx = (rexrect.ex+1)%this.dataY.length;
      mrrect.ex = (mrrect.ex)%this.dataY.length;
      mrrect.dx = mrrect.ex - mrrect.sx+1;
      mrrect.sy = this.dataY[(x+1)%this.dataY.length];

      print(`x ${x} ${mlrect.sx} ${mlrect.ex} ${lexrect.sx} ${lexrect.ex} ${rexrect.sx} ${rexrect.ex} ${mrrect.sx} ${mrrect.ex}`);

      if(mlrect.sx <= mlrect.ex)      // Check if there is a monotone to append on the left
        this.leftboxsnake.push(mlrect); // Prepend
      else
      {
        print("mlskip");
      } 
      this.leftboxsnake.push(lexrect); // Append the left extremum

      if(mrrect.sx <= mrrect.ex)      // Check if there is a monotone to append on the right
        this.rightboxsnake.unshift(mrrect); // Prepend
      else
      {
        print("mrskip");
      }
      this.rightboxsnake.unshift(rexrect); // Prepend the right extremum
      this.rightbasepoint = this.rightboxsnake[0].sx;
    }
  }

  if(this.usecircular==true)          // if we had a circular domain then we just decircularized
  {
    this.boxsnake = [...this.rightboxsnake, ...this.leftboxsnake ];             // Keep the non-cut ends together.
    this.rightboxsnake = this.boxsnake;
    this.leftboxsnake = this.boxsnake;
    this.usecircular = false;        // decircularized
    this.fixRectPoints(this.boxsnake,0);
    this.basepoint = this.boxsnake[0].sx;
    print("Decircularizing complete "+this.boxsnake.length );
  }

  this.integritycheck(this.rightboxsnake[0].sx,this.rightboxsnake,false);
  this.integritycheck(this.leftboxsnake[0].sx,this.leftboxsnake,false);

  print(`${this.leftboxsnake.length} ${this.rightboxsnake.length}`);
}


// 
// Test that checks the validity and integrity of a box snake structure in numerous ways.
// Purpose is to detect issues with surgery
// 

integritycheck(bp,rectangles,total=true)
{
  print("--integrity check! "+total+" "+" "+rectangles.length+" "+rectangles[0].sx);
  let ssx = bp;
  let totaldx = 0;
  let p = this.dataY.length;
  let r = rectangles.length;
  for(let i=0;i<rectangles.length;i++)
  {
    if(rectangles[i].sx >= p) printc("Iosx("+i+"): "+rectangles[i].sx+" "+p);
    if(rectangles[i].sx != ssx) printc("Isx("+i+"): "+rectangles[i].sx+" "+ssx);
    if(rectangles[i].dx != rectangles[i].ex-rectangles[i].sx+1) printc("Idx("+i+"): "+rectangles[i].dx+" "+(rectangles[i].ex-rectangles[i].sx+1));
    if(rectangles[i].ex != ssx+rectangles[i].dx-1) printc("Iex("+i+"): "+rectangles[i].ex+" "+(ssx+rectangles[i].dx-1)+" "+rectangles[i].dx);
    if(rectangles[i].ext && rectangles[i].sy != this.dataY[ssx%p]) printc("Isy("+i+"|"+ssx+"): "+rectangles[i].sy+" "+(this.dataY[ssx%p]));
    if(rectangles[i].ext && rectangles[i].ey != this.dataY[(ssx+rectangles[i].dx-1)%p]) printc("Iey("+i+"|"+((ssx+rectangles[i].dx-1)%p)+"): "+rectangles[i].ey+" "+(this.dataY[ssx+rectangles[i].dx-1]));
    if(rectangles[i].ext==false && i>1 && rectangles[(i-1)%r].ey!=rectangles[i].sy) printc("Iey("+i+"|"+(rectangles[(i-1)%r].ey)+"): "+rectangles[i].sy);
    if(rectangles[i].ext==false && i<r && rectangles[i].ey!=rectangles[(i+1)%r].sy) printc("Iey("+i+"|"+(rectangles[i].ey)+"): "+rectangles[(i+1)%r].sy);
    totaldx = totaldx+rectangles[i].dx;
    ssx = ssx + rectangles[i].dx;
  }
  if(total == true && totaldx != this.dataY.length)
    {
      printc("Itdx: "+totaldx+" "+this.dataY.length);
//      dumpdxprofile();
      printc("--------------------------");
    }
}


//
// Functions that allow redistributing flat regions between extrema and adjacent monotones.
// The definition of an extremum and monotone overlap along flats, therefore we can redistrute samples between them.
//

resizeFlatMembershipRightGrow(highlightbox)
{
//  print("GR> "+rectangles[highlightbox].ey+" "+this.dataY[rectangles[(highlightbox+1).mod(rectangles.length)].sx]);       
  if(this.boxsnake[highlightbox].ey==this.dataY[this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx] && this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx<this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].ex)
    {
 this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx=this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx+1;
      this.boxsnake[highlightbox.mod(this.boxsnake.length)].ex=this.boxsnake[highlightbox.mod(this.boxsnake.length)].ex+1;

//      print(rectangles[(highlightbox+1).mod(rectangles.length)].sx+" "+rectangles[highlightbox].ex);
      
    };
}

resizeFlatMembershipRightShrink(highlightbox)
{
//  print("SR< "+this.dataY[rectangles[highlightbox.mod(rectangles.length)].ex]+" "+this.dataY[rectangles[(highlightbox+1).mod(rectangles.length)].sx]);       
    if(this.dataY[this.boxsnake[highlightbox].ex]==this.dataY[this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx] && this.boxsnake[highlightbox].ex>this.boxsnake[highlightbox].sx)
    {
 this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx=this.boxsnake[(highlightbox+1).mod(this.boxsnake.length)].sx-1;
      this.boxsnake[highlightbox].ex=this.boxsnake[highlightbox].ex-1;
      
//      print(rectangles[(highlightbox+1).mod(rectangles.length)].sx+" "+rectangles[highlightbox].ex);
    }
}


resizeFlatMembershipLeftGrow(highlightbox)
{
//  print("GL> "+rectangles[highlightbox].sy+" "+this.dataY[rectangles[(highlightbox-1).mod(rectangles.length)].ex]);
  if(this.boxsnake[highlightbox].sy==this.dataY[this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex] && this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex>this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].sx)
    {
 this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex=this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex-1;
      this.boxsnake[highlightbox.mod(this.boxsnake.length)].sx=this.boxsnake[highlightbox.mod(this.boxsnake.length)].sx-1;

//      print(rectangles[(highlightbox-1).mod(rectangles.length)].ex+" "+rectangles[highlightbox].sx);
      
    };
}

resizeFlatMembershipLeftShrink(highlightbox)
{
//  print("SL< "+this.dataY[rectangles[highlightbox.mod(rectangles.length)].sx]+" "+this.dataY[rectangles[(highlightbox-1).mod(rectangles.length)].ex]);
  if(this.dataY[this.boxsnake[highlightbox].sx]==dataY[this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].sx] && this.boxsnake[highlightbox].sx<this.boxsnake[highlightbox].ex)
    {
 this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex=this.boxsnake[(highlightbox-1).mod(this.boxsnake.length)].ex+1;
      this.boxsnake[highlightbox].sx=this.boxsnake[highlightbox].sx+1;
      
//      print(rectangles[(highlightbox-1).mod(rectangles.length)].ex+" "+rectangles[highlightbox].sx);
    }
}

updateGlobalExtrema(newmincandidate, newmaxcandidate)
{
  if(newmaxcandidate>this.globalmax)
    this.globalmax = newmaxcandidate;     // We adjust the global max as needed. This is O(n) based on the length of the new data. If shifts are sufficiently short this is good news for computational cost.
  // This can be optimized further if the maximum is known ab initio for synthetic data. We will not cover this case.
  if(newmincandidate<this.globalmin)
    this.globalmin = newmincandidate;     // Keep inverting at O(1) cost.
  this.isconstfunc = (this.globalmax == this.globalmin);      // Keep processing constants at O(1).    
}

//
// Invert datasets and barcodes for duality/superlevel set computations
//

// Invert the sign of a data array. This for the purpose of the paper inverts order.
signInvertArray(arr)
{
  print(arr);
  arr = arr.map(d => { return -d; });
  print(arr);
  return arr;
}

// This is used for Superlevel Set Computation via Sign duality.
invertData()
{
  print("Data before inversion  "+dataY);
  dataY=signInvertArray(dataY);
  const swaptemp = this.globalmax;
  this.globalmax = -this.globalmin;       // No need to compute global maxima when they can be inverted from known global minima.
  this.globalmin = -swaptemp;
  print("Data after inversion  "+dataY);
}
// Exchange births and deaths of a bar. This is reversing the order of the bar.
invertBar(b)
{
  print("Original Bar  "+b[0]+" "+b[1]);
  let tempby=b[0][2];
  let tempbd=b[0][1];
  b[0][2]=-b[1][2];
  b[0][1]=-b[1][1]
  b[1][2]=-tempby;
  b[1][1]=-tempbd;
  print("Inverted Bar  "+b[0]+" "+b[1]);
}

// Exchanges births and deaths of all bars in a barcode.
invertBarcode()
{
  for(let i=0; i<this.barcode.length; i++)
  {
    invertBar(this.barcode[i]);  
  }
}

//
// Set of Levels computations
//

// Compute the Set of Levels from the data

// Find the location of an element in an array.
locationOf(element, array, start, end) {
  if(array.length==0) return 0;
  start = start || 0;
  end = end || array.length;
  var pivot = parseInt(start + (end - start) / 2, 10);
  if (array[pivot] === element) return pivot;
  if (end - start <= 1)
    return array[pivot] > element ? pivot - 1 : pivot;
  if (array[pivot] < element) {
    return locationOf(element, array, pivot, end);
  } else {
    return locationOf(element, array, start, pivot);
  }
}

// Construct the Set of Levels from the data
constructSetofLevels()
{
  this.setoflevels = [];
  for(let i=0;i<this.dataY.length;i++)
  {
    this.setoflevels = insertOrdered(this.dataY[i],this.setoflevels);
  }
}

//
// Illustrate variable x-embeddings of the data as invariant under order.
//

// Compute an example of x-axis perturbation (deviation from uniform embedding). Here we use sinusoudal but any perturbation that preserves order is permissible.

createXPerturbation()
{
  if(this.nopert==true)
  {
  for(let i=0; i<this.dataY.length;i++)
    this.xpert.push(1);
  }
  else
    for(let i=0; i<this.dataY.length;i++)
    {
      this.xpert.push(Math.sin(2*Math.PI*i/this.dataY.length*4));
    }
  }
}

export default LSP;
