//
// (Sub/Super)level Persistence of a finite time series that includes arbitrary flats
//
// Georg Essl & Robin Belton(February 2024-January 2025)
//
// Thanks to Nicole Sanderson for seeding the idea and early discussions.

// Known issues:
// computeBoxSnakes does not respect superlevelset direction in its embedded barcode computation, however it can still compute superlevelset persistence via Theorem 6.3 of Belton & Essl (2025).
//
// Incomplete implementations/fragments:
// Barcode from Merge Tree via local rule is a fragment. Correct local bars can be computed via the barcodefromrectangle algorithm.
// computePH_n() not working correctly for total (elder) bar. Correct elder bars can be computed via the MergeTree algorithm if needed.

//
// Import stuff from ringedbufferwebaudio.js
//
import { createAudioContext, realdataQueue } from "../ringbufferwebaudio/ringedbufferwebaudio.js"
import { RENDER_QUANTUM } from '../constants.js';
import FFT from "../fft.js";
import LSP from "./LevelSetPersistence.js";

// Instance of LevelSetPersistence (LSP) we are using.
let myLSP = null;

// Data related to playing audio
let audioContext = null;
let isPlaying = false;

let shiftkeys = true;

// Global states
let usecircular = false;          // Domain is linear: false  Domain is circular: true
let startfunc = 32;//20;               // Which function to launch with
let startfunc2 = 33;              // Files!
let currentindex = 32;            // Stores the actually used function as may be changed by dropdown
//let startfunc = Math.floor(Math.random()*18);
let savesvg = 0;                  // Save SVG at launch (can also be achieved by '=' key)
let rendersvg = 0;                // Use SVG rendering to allow SVG saving
let label = "circ";               // A custom string to embed in the save file name.
var levelset = 0;                 // Starting level set
let csplitpoint = 0;//dataY.length/2-1;  // Point in the data after which the data will be split in surgery (key 'S')
//let shiftlength = 4;              // Amount of data to shift per step
let shiftlength = 16;//32;              // Amount of data to shift per step
let showelder = false;             // Computer Elder Barcode (via modified Barychikov's algorithm)
let overridemergetreeelder = false;  // Computer Elder barcode from Merge Tree

let barcodemode = "MergeTreeElder";
let elderfilename = [];             // Add test to SVG file name to indicate if local or elder barcode rule was used.
elderfilename[false]="-local";
elderfilename[true]="-elder";

let highlightbox = 1;               // A local box snake rectangle is selected. Show it highligted? (0: no, 1: yes) GEORG: MAKE BOOLEAN

let drawsplitbox = false;           // see also drawsplitline in discretegraph

// Array of currently analysed finite time series window

// GEORG current data has to be powers of 2. REVISE?
let dataY = [];           // Currently actibe data set for computations/display
// Data examples

// Time/Frequency Domain Data
let computeFFT = false;
let tdataY = [];
let fdataY = [];
let fdataP = [];

// Data examples
let dataYa = [];           // Array of data examples to select.
let functionName = [];     // Name associated with each example. Same index as dataYa

// Our data examples are usually designed to range from -180 to 180 so 180 is a known normalizing divisor, or allows us to scale unit scale data to the one we use. Graphing assumes this scale.
let normalizer = 180;

// Current examples range from -180 to 180.
// We use managable integer range to make hand crafting function examples easy.
// 360 is divisible by 2, 3, 4, 5, and 6 (convenient!)
// (try doing it for normalized data and you'll understand!)

// Many examples of functions

functionName[0] = "Some Function Shape";
//dataYa[0] = [0,0,-50,-100,-150,-180,-180,-140,-90,-40,0,0,50,150,150,180,180,140,140,40,0,0,0,-50,-100,-40,0,50,0,-50,-22.5,0]
dataYa[0] = [0,0,-50,-100,-150,-180,-180,-140,-90,-40,0,0,50,100,150,180,180,140,80,40,0,0,0,-50,-100,-40,0,50,0,-50,-22.5,0]
//dataYa[0] = [12,12,-60,-108,-156,-180,-180,-132,-84,-36,12,12,60,108,156,180,180,132,84,36,12,12,12,-60,-108,-36,12,60,12,-60,-12,12]
functionName[1] = "Widening Rectangular Wave";
dataYa[1] = [180,-180,180,180,-180,-180,180,180,180,-180,-180,-180,180,180,180,180,-180,-180,-180,-180,180,180,180,180,180,-180,-180,-180,-180,-180,-180,180];
functionName[2] = "Impluse Chirp";
dataYa[2] = [180,0,0,0,0,0,0,180,0,0,0,0,0,180,0,0,0,0,180,0,0,0,180,0,0,180,0,180,0,180,0,180];
functionName[3] = "Impulse Chirp with leading zero flat";
dataYa[3] = [0,0,180,0,0,0,0,0,0,180,0,0,0,0,0,180,0,0,0,0,180,0,0,0,180,0,0,180,0,180,0,180];
functionName[4] = "Constant zero";
dataYa[4] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
functionName[5] = "Oscillating Impulse Chirp";
dataYa[5] = [-180,0,0,0,0,0,0,180,0,0,0,0,0,-180,0,0,0,0,180,0,0,0,-180,0,0,180,0,180,0,180,0,180];
functionName[6] = "Decaying Impulse Chirp";
dataYa[6] = [-180,0,0,0,0,0,0,180,0,0,0,0,0,-170,0,0,0,0,170,0,0,0,-160,0,0,160,0,150,0,140,0,130];
functionName[7] = "Ascending Impulse Chirp";
dataYa[7] = [-150,0,0,0,0,0,0,150,0,0,0,0,0,-160,0,0,0,0,160,0,0,0,-170,0,0,170,0,175,0,180,0,185];
/*functionName[8] = "Negative Delay Impulse";
dataYa[8] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-180,0,0,0];
functionName[9] = "Positive Delay Impulse";
dataYa[9] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,180,0,0,0];*/
functionName[8] = "Negative Delay Impulse";
dataYa[8] = [0,0,0,0,0,0,0,0,0,0,0,0,-180,0,0,0];
functionName[9] = "Positive Delay Impulse";
dataYa[9] = [0,0,0,0,0,0,0,0,0,0,0,0,180,0,0,0];
functionName[10] = "Alternating 2-Flats";
dataYa[10] = [0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,0,0,0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,-180,-180];
functionName[11] = "Alternating 2-Flats (long)";
dataYa[11] = [0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,0,0,0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,0,0,0,0,180,180,0,0,-180,-180,0,0,180,180,0,0,180,180,0,0,-180];
functionName[12] = "Decaying Flat Squares";
dataYa[12] = [0,0,180,180,0,0,-120,-120,0,0,70,70,0,0,-30,-30,0,0,10,10,0,0,-5,-5,0,0,4,4,0,0,0,-3,-3,0,0,2,2,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
functionName[13] = "Ascender";
dataYa[13] = [-180,10,-170,20,-160,30,-150,40,-140,50,-130,60,-120,70,-110,80,-100,90,-90,100,-80,110,-70,120,-60,130,-50,140,-40,150,-30,160];
functionName[14] = "AscenderS";
dataYa[14] = [10,-170,20,-160,30,-150,40,-140,50,-130,60,-120,70,-110,80,-100,90,-90,100,-80,110,-70,120,-60,130,-50,140,-40,150,-30,160,-20];
functionName[15] = "Descender";
dataYa[15] = [180,-10,170,-20,160,-30,150,-40,140,-50,130,-60,120,-70,110,-80,100,-90,90,-100,80,-110,70,-120,60,-130,50,-140,40,-150,30,-160];
functionName[16] = "Ascender2";
dataYa[16] = [0,-180,10,-170,20,-160,30,-150,40,-140,50,-130,60,-120,70,-110,80,-100,90,-90,100,-80,110,-70,120,-60,130,-50,140,-40,150,-30];
functionName[17] = "Descender2";
dataYa[17] = [0,180,-10,170,-20,160,-30,150,-40,140,-50,130,-60,120,-70,110,-80,100,-90,90,-100,80,-110,70,-120,60,-130,50,-140,40,-150,30];
functionName[18] = "Sinusoid";
dataYa[18]=[];
functionName[19] = "Balanced Pulse";
dataYa[19]=[];
functionName[20] = "Some Function Shape (shifted)";
dataYa[20] = [0,0,-50,-100,-40,0,50,0,-50,-20,0,0,0,-50,-100,-150,-180,-180,-140,-90,-40,0,0,50,100,150,180,180,140,90,40,0];
functionName[21] = "All Flat Types";
dataYa[21] = [0,0,-50,-100,-40,0,0,0,-50,-20,0,0,0,40,75,110,150,150,120,60,0,0,35,70,115,150,140,110,65,30,0,0];
functionName[22] = "ElderGame";
dataYa[22] = [170,-1,135,44,90,89,45,134,0,179,-45,134,-90,89,-135,44,-170,-1,-135,-46,-90,-91,-45,-136
,0,-180,45,-136,90,-91,135,-46];
//dataYa[20] =[180,-1,135,44,90,89,45,134,0,189,-45,134,-90,89,-135,44,-180,-1,-135,-46,-90,-91,-45,-136,0,-191,45,-136,90,-91,135,-46];
functionName[23] = "ElderDescender";
dataYa[23] = [180,-170,160,-60,170,-150,140,-40,150,-130,120,-20,130,-110,100,-10,110,-80,80,-10,90,-60,60,-0,70,10,40,-40,50,20,30,-20];
functionName[24] = "ConstantHomology";
dataYa[24] = [-175,-175,0,0,0,-175,-175,-175,180,180,180,0,0,0,180,180];
functionName[25] = "Surgery (Monotone)";
dataYa[25] = [180,160,140,120,100,80,60,40,20,0]; // EMonotone
functionName[26] = "Surgery (constant)";
dataYa[26] = [0,0,0,0,0,0,0,0,0,0]; // Constant Same Level
functionName[27] = "Surgery (constant split)";
dataYa[27] = [0,0,0, 0, 0,180,180,180,180,180]; // Constant Split Level
functionName[28] = "Surgery (EE diff)";
//dataYa[28] = [90,90, 90, 0, 0,180,180,90,90,90]; // Differing Extrema Level
dataYa[28] = [90,90, 90, 180, 180,0,0,90,90,90]; // Differing Extrema Level
functionName[29] = "Surgery (EE Same)";
dataYa[29] = [0,60, 60,120,180,180,120,60,60,0]; // Same level Extrema
functionName[30] = "Surgery (EM)";
dataYa[30] = [0,90, 90,180,180,120,120,60,0,0]; // Extrema and Monotone
//functionName[31] = "Global Max in Boundary";
//dataYa[31] = [180,0, 0,0,0,90,90,0,0,180]; // Global maxima in boundary
functionName[31] = "Global Max in Boundary";
dataYa[31] = [180,0, 0,0,0,90,90,0,0,-180]; // Global maxima in boundary
functionName[32] = "GenerativeStream";
dataYa[32] = [0];

let dostreaming = false;      // Currently we have that data that is at cbufferindex being played will automatically trigger streaming.
let cbufferpos = 0;
let cbufferlen = 2048;
let cbufferindex = 32; // Index in the function/dataYa table for the streaming circular buffer

// Parameters for fm/am waveform generation
// Used for streaming buffer examples
let fmphase = 0;
let modphase = 0;
//let fmomega = 172.265625/44100;
//let fmomega = 110/44100; //172.265625/44100;///1.25;
let fmomega = 1/cbufferlen/2;
let fmH = 0.01;// 0.03;
//let modomega = 55/44100;//172.26562/2/44100;///1.25;
let modomega = 1/cbufferlen*2;
let amphase = 0;
let amomega = 1/cbufferlen;

// Iterative Phase version of FM.
function incrementFMPhase()
{
  fmphase = fmphase + fmomega + fmH*Math.sin(2*Math.PI*modphase); // FM is a simple sinusoidal phase perturbed by another oscillator
  modphase = modphase + modomega;                                 // Modulator is just a simple sinusoidal phase
  amphase = amphase + amomega;
  return Math.sin(2*Math.PI*amphase)*Math.sin(2*Math.PI*fmphase);                             // Project out through sinusoid
}

// Circular buffer loaded with an incremental function
function progressCircularBuffer(len)
{
  for(let i=0; i<len; i++)
    dataYa[cbufferindex][(i+cbufferpos)%cbufferlen]= normalizer*incrementFMPhase();
  cbufferpos = (cbufferpos+len)%cbufferlen;
  print("cbp = "+cbufferpos+"  "+len); // Tracks progression of circular buffer for debugging purposes, deactivated if print does nothing.
}

// First setup of a circular buffer
function setupCircularBuffer()
{
  cbufferpos = 0;
  progressCircularBuffer(cbufferlen);
}

// Allow loop files to be loaded at the end of the example array

let fileindex = dataYa.length;
functionName[fileindex] = "File";
dataYa[fileindex] = [];

// Indices 18 and 19 are reserved for functionally defined examples
let genindex1 = 18;
let genindex2 = 19;

// Notes from the sound file library (AKWF)
// oscchip 75 -> is a decent rigidity example (hard to deform audio)

// Below are utility function wrappers to allow enabling/disabling debug messages

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

//
// Create data set functionally. This example contains a cosine function with a discrete frequency change mid-data.
//

//let slen = 256;
let slen = 128;               // Length of the functional data set
function createSplitSinusoid()
{
  /*
  for(let i=0; i<slen/2;i++)
    {
      dataYa[genindex1][i]=(180-(slen/2-i)*120/slen)*Math.cos(2*48*Math.PI*i/(slen*8));
    }
  for(let i=slen/2; i<slen;i++)
    {
      dataYa[genindex1][i]=(180-(slen-i)*120/slen)*Math.cos(2*48*Math.PI*i/(slen*8));
    }
      */
    for(let i=0; i<slen;i++)
      {
        dataYa[genindex1][i]=(180-(slen-1-i)*120/slen)*Math.cos(2*48*Math.PI*i/(slen*8));
      }
}

// Various functional data set generators

// Create data consisting of mixture of 3 sinusoids
function createThreeSinusoid()
{
  for(let i=0; i<slen;i++)
    {
      dataYa[genindex1][i]=180/3*(Math.sign(Math.cos(2*64*Math.PI*i/(slen*8)))+1.5*Math.sign(Math.cos(2*32*Math.PI*i/(slen*8)))+1/2*Math.sign(Math.cos(2*128*Math.PI*i/(slen*8))));
    }
}

// Create data consisting of mixture of 2 sinusoids
function createSinusoid()
{
  for(let i=0; i<slen;i++)
    {
      dataYa[genindex1][i]=180/2*((Math.cos(2*64*Math.PI*i/(slen*8)))+(Math.cos(2*32*Math.PI*i/(slen*8))));
    }
}

// Create data consisting of one sinusoids
function createSinusoid_o()
{
  for(let i=0; i<slen;i++)
    {
      dataYa[genindex1][i]=180*((Math.cos(2*64*Math.PI*i/(slen*8))));
    }
}

// Create data consisting of one sinusoids (different frequency)
function createSinusoid_o2()
{
  for(let i=0; i<slen;i++)
    {
      dataYa[genindex1][i]=-180*((Math.sin(2*16*Math.PI*i/(slen*8))));
    }
}

function createWideSpectrum()
{
  for(let i=0; i<slen/2;i++)
    {
      dataYa[genindex2][i]=-180*((Math.sin(2*16*Math.PI*i*2/(slen*32))*Math.sin(2*16*Math.PI*i*2/(slen*32))));
    }

}

//
// Shifting/Streaming functions. These function provide new data that is "shifted in" in a shift step of the length asked by the particular use case (step shift/streaming).
//

// Shift an incremental oscillator for streaming.
function generateStreamingShift()
{
  print("genshift");
  let newDataY = Array(RENDER_QUANTUM*us);
  for(let i=0; i<RENDER_QUANTUM*us; i++)
  newDataY[i]= normalizer*incrementFMPhase();

  return newDataY;
}

// Shift a linearly decaying cosine.
function generateCosineShift()
{
  let newDataY = Array(shiftlength);
  for(let i=0;i<shiftlength;i++)
  {
    newDataY[i]=(180-i*60/shiftlength)*Math.cos(2*64*Math.PI*i/(slen*8));
  }

  return newDataY;
}

// Just shift in noise
function generateNoiseShift()
{
  let newDataY = Array(shiftlength);
  let rnd = Math.floor(Math.random()*360-180);
  for(let i=0;i<shiftlength;i++)
  {
    newDataY[i]=rnd;
    rnd = Math.floor(Math.random()*360-180);
  }

  return newDataY;
}


// Just shift in flats at noise level
function generateFlatNoiseShift()
{
  let newDataY = Array(shiftlength);
  let rnd = Math.floor(Math.random()*360-180);
  for(let i=0;i<shiftlength;i++)
  {
    newDataY[i]=rnd;
  }

  return newDataY;
}

// Generate Shifting Data. This can be altered by function or use a shared new shifting data.
function generateShiftData()
{
  if(currentindex == cbufferindex)
    return generateStreamingShift();
  else if(currentindex == genindex1)
    return generateCosineShift();
  else if(currentindex = 0)
    return generateFlatNoiseShift();
  else
    return generateNoiseShift();
}

//
// Layout constants
//

// Various of these have been used to create figures.

//let totalw = 800;            // Total width of used canvas drawing area
//let totalw = window.innerWidth/6;// Divisor is for rendering surgery figures
//let totalw = window.innerWidth/2;// Divisor is for rendering surgery figures//800;
//let totalw = window.innerWidth/3;// Divisor is for rendering surgery figures//800;
let totalw = window.innerWidth;// Divisor is for rendering surgery figures//800;
//let totalh = window.innerHeight-(bottommargin+bottomconnect/2)*2-32;
let totalh = 440;             // Total height of used canvas drawing area
let leftmargin = 20;          // Left margin for axis
let rightmargin = window.innerWidth/6;//20;//20;//200;//200;   // Right margin for barcodes
let bottommargin = 20;        // Bottom margin for axis
let bottomconnect = 20;       // Bottom area for level set line graph
let innerw = totalw-leftmargin/*-dotsize*/-rightmargin;   // Width of graphing area for data
let innerh = totalh-bottommargin-bottomconnect*2;         // Height of graphing area for data

// Size of dots in graph rendering, this is set differently for different use case (marge for certain figures, small for interactive)
let bubblesize = 6; //12;

// Box snake deformations
//
let defx = 0; let defy = 0;         // These are used to deform box snake rectangles "statically"
let showdeform = false;             // If true computes a linear deformation based on defx and defy on startup.

// Deformatble interactions
let globaledit = true;              // If true deformations of box snakes effect every deformable box. Else it is local to one box.
let outofrectedits = true;          // Do interactions allow and clip edits outside of actual rectangles. Useful for interactive demos.

let dofourier = false;              // Use frequency domain (via FFT) on startup

let maxmax = Number.NEGATIVE_INFINITY;//-200;  // Find the global maximum, seeded by what should exceed the data minimum.

// Web UI element handles
let audiofileinput;         // handle for web page button to load audio files.
let dataselectmenu;         // handle for the web page drop down menu to select data sets

// Split Point location in data.
// If circular it will split at the end of the data.
// If linear it will split at a given split point location via csplitpoint
let splitpoint = 0;

// Help compare FFT outputs for debugging purposes
let fftout;

// Compute FFT Normalization factor (Parseval Sum)
function ParsevalSum(arr)
{
  return arr.reduce((partialSum, a) => partialSum + Math.abs(a), 0);
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

// Utility function supporting to launch on specific data for slides and posters
var copyFunction_s = function ()
{
  copyFunction_f(dataselectmenu.selected());     // Get dataset from selected menu item
}

var copyFunction_n = function ()
{
  copyFunction_f(functionName[startfunc]);
}

var copyFunction_n2 = function ()
{
  copyFunction_f(functionName[startfunc2]);
}


// Copy example data for current computation and compute sublevelset persistence on it
// It does nothing if data has not changed.
// In visualization this is called per visual rendering.
function copyFunction_f(f)
{
  // Only copy sample data if it's different from the currently used dataset
  if(p5.currentfunc != f)
    {
      forcecopyFunction_f(f);
    }
}

// If data changed derivative results are (re)computed.
function forcecopyFunction_f(f)
{
  let i = functionName.indexOf(f);
  myLSP.dataY = dataYa[i];
  myLSP.setData(myLSP.dataY,usecircular);
  p5.currentfunc = f;
  currentindex = i;
  // For web application this logs the starting or switch state.
  console.log(p5.currentfunc);
  console.log(currentindex);
  console.log(barcodemode);
  console.log(myLSP.usecircular?"circular":"linear");
  console.log(myLSP.globalmax);

  if(computeFFT==true)         // If we are computing FFTs, do it!
  {
    // Compute FFT on new data.
    const myFFT = new FFT(myLSP.dataY.length);
    normalizer = ParsevalSum(myLSP.dataY);
    var ip = myLSP.dataY;
    if(normalizer != 0)
      ip = myLSP.dataY.map((element) => element / normalizer);
    fft.forward(ip); // compute FFT
    var op = fft.real; // output array
    tdataY = myLSP.dataY;
    // Not renormalizing instead we scale to conventional data size
    // var fnormalizer = ParsevalSum(op);
    fdataY = op.map((element) => element *normalizer);

    if(dofourier==true)      // Are we using the computed as actual data for further processing?
      myLSP.dataY = fdataY;        // Yes: frequency domain
    else
      myLSP.dataY = tdataY;        // No: keep time domain
  }
  else
    tdataY = myLSP.dataY;          // We only have time domain data
  
  myLSP.createXPerturbation();     // Compute x-axis perturbation for the current data (length can have changed)
  myLSP.constructSetofLevels();    // Compute set of levels for the current data. Not plotted this can be skipped.
  csplitpoint = myLSP.dataY.length/2-1;   // Compute a middle split point from data in case we want to split into two separate graphs

//  myLSP.computePH();             // If snake boxes are not of interest just barcodes, pick a way to compute barcodes directly.
  myLSP.computeSnakeBoxes();       // Compute the box snake structure for the current data set
  myLSP.mergeTreefromSnakeBox();   // Compute the merge tree from the box snake
  myLSP.computeBarcode();          // Compute bar codes from a selected method
}

//
// Load an audio file into a data buffer
//

// Utility: Compute the nearest (lower) power of 2 (fast method from stackoverflow)
// https://stackoverflow.com/questions/2679815/previous-power-of-2
function flp2 ( x)
{
    x = x | (x >> 1);
    x = x | (x >> 2);
    x = x | (x >> 4);
    x = x | (x >> 8);
    x = x | (x >> 16);
    return x - (x >> 1);
}

// Load an audio file of the web server via filename into a data array utilizing WebAudio API. Used to allow slides/poster to load a specific file of interest.
// WARNING: THis has special code to help convert a large dataset that is 600 bytes by brute force interpolating it into 512 buffers for FFT compatibility.
async function loadSoundFile(filename)
{
  let audioCtx = new AudioContext({sampleRate:44100});
  console.log(filename);
  console.log("https://127.0.0.1:8080/"+filename);

  let audioData = await fetch("https://127.0.0.1:8080/"+filename).then(r => r.arrayBuffer());
  let decodedData = await audioCtx.decodeAudioData(audioData); // audio is resampled to the AudioContext's sampling rate

  console.log(decodedData.length, decodedData.duration, decodedData.sampleRate, decodedData.numberOfChannels);

  let float32Data = decodedData.getChannelData(0); // Float32Array for channel 0
  // WARNING: 600 samples long data has special handling due to the use of the AKWF library for demos
  if(float32Data.length==600)
  {
    dataYa[fileindex] = new Array(512);
    console.log("Sample Conversion 600->512");
    for(let i=0;i<512;i++)
    {
      dataYa[fileindex][i]=float32Data[Math.floor(i*600/512)];
    }
  }
  else // Other data lengths are truncated to powers of 2 to be FFT conforming. Some applications may prefer padding.
    dataYa[fileindex] = float32Data.slice(0, flp2(decodedData.length));

  let ymax = Math.max.apply(null, dataYa[fileindex].map(Math.abs));
  dataYa[fileindex] = dataYa[fileindex].map((element) => element/ymax*normalizer);

  p5.currentfunc= "";       // Make sure that all data structures are updated and recomputed
}

// This is the function called from the audio file load web page button
async function handleSoundFile(file) {
  print(file.type);
  if (file.type === 'audio')
  {
    console.log(file.name+" "+file.file.webkitRelativePath+" "+file.file.name);
    let audioData = await fetch(file.data).then(r => r.arrayBuffer());

    let audioCtx = new AudioContext({sampleRate:44100});

    let decodedData = await audioCtx.decodeAudioData(audioData); // audio is resampled to the AudioContext's sampling rate

    console.log(decodedData.length, decodedData.duration, decodedData.sampleRate, decodedData.numberOfChannels);

    let float32Data = decodedData.getChannelData(0); // Float32Array for channel 0
    // WARNING: 600 samples long data has special handling due to the use of the AKWF library for demos
    if(float32Data.length==600)
    {
      dataYa[fileindex] = new Array(512);
      console.log("Sample Conversion 600->512");
      for(let i=0;i<512;i++)
      {
        dataYa[fileindex][i]=float32Data[Math.floor(i*600/512)];
      }
    }
    else
      dataYa[fileindex] = float32Data.slice(0, flp2(decodedData.length));

    let ymax = Math.max.apply(null, dataYa[fileindex].map(Math.abs));
    dataYa[fileindex] = dataYa[fileindex].map((element) => element/ymax*normalizer);

    p5.currentfunc= "";     // Make sure that all data structures are updated and recomputed
  }
}

function setupFunctionShapes()
{
  // Populate genindex1 data
  createSplitSinusoid();
//  createSinusoid_o2(); // If you want to try some of the other ones.

  // Populate genindex2 data
  createWideSpectrum();

  // Bootstrap circular buffer for streaming
  setupCircularBuffer();
}

function setupUIElements(p5)
{
  // Create dropdown menu
  dataselectmenu = p5.createSelect();
  // Disable key input on selector
  dataselectmenu.elt.onkeydown=function (e)
  {
    if (!e) {
      e = window.event;
    }
    e.returnValue = false;
    e.cancel = true;
  }
  print(dataselectmenu); // Debug what menu options are populated

  dataselectmenu.position(totalw/2-280, p5.myCanvas.elt.getBoundingClientRect().top+totalh+(bottommargin+bottomconnect/2)*2);

  // Add function options.
  for(let i=0;i<functionName.length;i++)
     {
      dataselectmenu.option(functionName[i]);
     }

  // Set the selected option to starting function (startfunc index)
  dataselectmenu.selected(functionName[startfunc]);

  audiofileinput = p5.createFileInput(handleSoundFile);
  audiofileinput.position(totalw/2,p5.myCanvas.elt.getBoundingClientRect().top+totalh+(bottommargin+bottomconnect/2)*2);
}

// Use copyFunction for general compying to be overloaded with specific version for slides/posters/etc
var copyFunction;


// p5 code structure code

// setup functions as required by p5
// these are wrappers for different uses, generic, specific slides, posters etc.
function setup_generic(p5,mythis)
{
  if(savesvg==1 || rendersvg==1)
    {
      p5.myCanvas = p5.createCanvas(totalw, totalh, p5.SVG); // Create SVG Canvas, allows easy generation of figures. This is slow and not good for realtime audio use.
    }
    else
      p5.myCanvas = p5.createCanvas(totalw, totalh);         // Use standard canvas rendering for fast rendering. For realtime audio use. Still potentially slow. Consider no graphics updates.

  InstancedSketchGeneric.canvas=p5.myCanvas;
 
  myLSP = new LSP();

  setupFunctionShapes();
  setupUIElements(p5);

  p5.currentfunc = "";
  copyFunction = copyFunction_s; // Want Selector

  // Copy selected data
  copyFunction();
  if(showdeform) // This is for rendering static figures
    linearDeform(1,defx,defy);

  bubblesize = 12;
  // Instantiate main graph
  p5.maingraph = new disGraph(p5,totalw/2,totalh,leftmargin,rightmargin);
  p5.maingraph.setRootPos(0,0);
  p5.maingraph.setBubbleSize(bubblesize);
  p5.maingraph.setDrawLineLevel(true);
  // Instantiate secondary graph for second visualization in case of splits
  p5.secondgraph = p5.maingraph.clone();
  p5.secondgraph.setRootPos(totalw/2,0);
  p5.secondgraph.setBubbleSize(bubblesize);
  // Instantiate GUI to control visualization

  /*
  // UI to select graph settings, currently not working.
  p5.mySketch = mythis;
  gui = p5.createGui(InstancedSketchGeneric);//,'Graph Visibility');
  p5.gui = p5.createGui(mythis);//,'Graph Visibility');
  p5.gui.setPosition(totalw-130,20);
  p5.gui.addObject(p5.maingraph.paramstates);
  p5.sliderRange(-180, 180, 1);
  p5.gui.addGlobals('levelset');
  p5.gui.collapse();
  */
}

// Setup function are needed by p5
// These are different setups for different uses (poster, splides, standalone etc)
function setup_poster(p5)
{
  let p_id = document.getElementById("sublevelposter");
  console.log("ID "+p_id)
  if(p_id)
  {
    let p_args = p_id.getAttribute('data-args');
    totalh = window.innerHeight*3.0/3.7-(bottommargin+bottomconnect/2)*2-32;//document.getElementById('sublevelposter').clientHeight;
    totalw = window.innerWidth;// Divisor is for rendering surgery figures//800;
    innerh = totalh-bottommargin-bottomconnect*2;
    innerw = totalw-leftmargin/*-dotsize*/-rightmargin;
  //  let totalh = window.innerHeight-(bottommargin+bottomconnect/2)*2-32;//440;
    
    p5.myCanvas = p5.createCanvas(totalw, totalh);
    console.log("POSTER "+p_args);
    p5.myCanvas.parent('sublevelposter');
  }
  else
    console.log("POSTER FAIL");

  setupFunctionShapes();
  setupUIElements(p5);
  p5.currentfunc = "";
  copyFunction = copyFunction_s; // Want Selector
  console.log("LOADING SOUND FILE");
  loadSoundFile("/WebAudio/AKWF/AKWF_bw_blended/AKWF_blended_0008.wav");    // Example of loading a specific audio file for a poster at launch
  copyFunction();
  p5.maingraph = new disGraph(p5,totalw/2,totalh,leftmargin,rightmargin);
  p5.maingraph.setRootPos(0,0);
  p5.maingraph.setBubbleSize(bubblesize);
}

function setup_slide1(p5)
{
  let p_id = document.getElementById("sublevel1");
  console.log("ID "+p_id)
  if(p_id)
    {
      let p_args = p_id.getAttribute('data-args');
      totalh = window.innerHeight-(bottommargin+bottomconnect/2)*2-32;//document.getElementById('sublevelposter').clientHeight;
      innerh = totalh-bottommargin-bottomconnect*2;
      totalw = window.innerWidth;// Divisor is for rendering surgery figures//800;
      innerw = totalw-leftmargin/*-dotsize*/-rightmargin;
        
      p5.myCanvas = p5.createCanvas(totalw, totalh);
      console.log("SUBLEVEL1-reveal "+p_args);
      p5.myCanvas.parent('sublevel1');
    }
    else
      console.log("SLIDE1 FAIL");

  setupFunctionShapes();
  p5.currentfunc = "";
  copyFunction = copyFunction_n; // No selector
  copyFunction();
  p5.maingraph = new disGraph(p5,totalw/2,totalh,leftmargin,rightmargin);
  p5.maingraph.setRootPos(0,0);
  p5.maingraph.setBubbleSize(12);
  p5.maingraph.setDrawRect(false);
  p5.maingraph.setDrawLineLevel(true);
  p5.maingraph.setDrawSubLevelSet(true);
  p5.maingraph.paramstates.drawimpulses = true;
  p5.maingraph.paramstates.drawalllines = false;
  p5.maingraph.paramstates.drawdots = true;
  p5.maingraph.dotsubsample = 1;
}

function setup_slide2(p5)
{
  let p_id = document.getElementById("sublevel2");
  console.log("ID "+p_id)
  if(p_id)
    {
      let p_args = p_id.getAttribute('data-args');
      totalh = window.innerHeight*3.0/3.7-(bottommargin+bottomconnect/2)*2-32;//document.getElementById('sublevelposter').clientHeight;
      innerh = totalh-bottommargin-bottomconnect*2;
      totalw = window.innerWidth;// Divisor is for rendering surgery figures//800;
      innerw = totalw-leftmargin/*-dotsize*/-rightmargin;
      
      p5.myCanvas = p5.createCanvas(totalw, totalh);
      console.log("SUBLEVEL2-reveal "+p_args);
      p5.myCanvas.parent('sublevel2');
    }
    else
      console.log("SLIDE2 FAIL");

  setupFunctionShapes();
  p5.currentfunc = "";
  copyFunction = copyFunction_n2; // No selector
  console.log("LOADING SOUND FILE 1");
  loadSoundFile("/WebAudio/AKWF/AKWF_bw_blended/AKWF_blended_0008.wav");
  copyFunction();
  p5.maingraph = new disGraph(p5,totalw/2,totalh,leftmargin,rightmargin);
  p5.maingraph.setRootPos(0,0);
  p5.maingraph.setBubbleSize(bubblesize);
  p5.maingraph.setDrawLineLevel(false);
  p5.maingraph.setDrawSubLevelSet(false);
  p5.maingraph.paramstates.drawimpulses = false;
  p5.maingraph.paramstates.drawdots = false;
  p5.maingraph.dotsubsample = 16;
}

// draw functions are frame renderers for p5.
// These are different draws for different uses (poster, splides, standalone etc)
function draw_slide(p5)
{
//  copyFunction();     // This slide never changes data so this call is unnecessary
  p5.background(255);
  if(usecircular == true)
    splitpoint = myLSP.dataY.length-1; // rectangles[0].sx;//dataY.length-1;//0;//rectangles[0].sx + 31;
  else
    splitpoint = csplitpoint;
    if(showelder)
    myLSP.computePH_orig();           // Slide only needs barcodes so no other structures are computed
    
//  if(dataY.length<=512)       // We assume data sizes so no need to check
    {
    p5.maingraph.setSize(totalw,totalh,leftmargin,rightmargin);
    p5.maingraph.setAllData(myLSP.dataY,myLSP.boxsnake,myLSP.barcode,myLSP.setoflevels,myLSP.xpert,usecircular,0);
    p5.maingraph.drawGraph(levelset,splitpoint);
    }
    if(isPlaying)              // Slide can decide to start playing audio when it shows
      playAudioData();
}

// p5.js draw function, that refreshes at each frame
let dcnt=0;             // Display countdown. If 0 renders a display frame

function draw_generic(p5)
{
  copyFunction();

  if(dcnt==0)
  {
    p5.background(255);
    if(usecircular == true)
      splitpoint = myLSP.dataY.length-1; // rectangles[0].sx;//dataY.length-1;//0;//rectangles[0].sx + 31;
    else
      splitpoint = csplitpoint;

    if(showsplit) // Are we drawing two graphs for a surgically split data set? Yes!
    {  
      p5.maingraph.setSize(totalw/2,totalh,leftmargin,rightmargin)
      p5.maingraph.setAllData(leftdata,leftrectangles,leftbarcode,myLSP.setoflevels,myLSP.xpert,usecircular,0);
      p5.maingraph.drawGraph(levelset,splitpoint);

      p5.secondgraph.setSize(totalw/2,totalh,leftmargin,rightmargin);
      p5.secondgraph.setAllData(rightdata,rightrectangles,rightbarcode,myLSP.setoflevels,myLSP.xpert,usecircular,rightbasepoint);
      p5.secondgraph.drawGraph(levelset,splitpoint);

      // This helps draw a dashed line location after a linear split between the two graphs (for figures)
      if(drawsplitbox==true)
      {
        p5.push();
        p5.translate(0,innerh/2);
        p5.noStroke();
        p5.maingraph.setLineDash([10, 10]);
        p5.stroke(0,0,0,128);
        let xmid = totalw/2;
        p5.line(xmid,20,xmid,-200);
        p5.noStroke();
        p5.maingraph.setLineDash([]);
        // And draw a bounding rectangle for the figure
        p5.stroke(0,0,0,128);
        p5.noFill();
        p5.rect(0,-220,totalw,260);
        p5.pop();
      }
    }
    else // Are we drawing two graphs for a surgically split data set? No! Just one graph.
    {
      p5.maingraph.setSize(totalw,totalh,leftmargin,rightmargin);
      p5.maingraph.setAllData(myLSP.dataY,myLSP.boxsnake,myLSP.barcode,myLSP.setoflevels,myLSP.xpert,myLSP.usecircular,0);
      p5.maingraph.drawGraph(levelset,splitpoint);
      if(drawsplitbox==true) // And draw a bounding rectangle for the figure, the dashed line in this case is drawn inside discretegraph.js
      {
        p5.push();
        p5.translate(0,innerh/2);
        p5.stroke(0,0,0,128);
        p5.noFill();
        p5.rect(0,-220,totalw,260);
        p5.pop();
      }
    }
    p5.maingraph.plotfullMergeTree(myLSP.mergetree);
  }
 
  if(savesvg == 1)   // This is used if an SVG should be saved without rendering any interactivity. Used for making specific figures.
  {
    save(p5.currentfunc+"-("+levelset+")+("+defx+"_"+defy+")"+drawrect+label+noiselevel+"-preshift.svg"); // give file name
    noLoop(); // Disable frame updates.
  }

  if(waitcnt==0 && doshift!=0) // Are we waiting for a shift update?
  {
    let newDataY = generateShiftData();  // Get data to be shifted in
    let [newmaxcandidate,newmincandidate] = getGlobalMinMax(newDataY);

    myLSP.updateGlobalExtrema(newmincandidate,newmaxcandidate);

    print(doshift);     // To help debug shift directions

    if(doshift==-1)               // shift left
      myLSP.shiftDataLeft(newDataY);
    else if(doshift==1)           // shift right
      myLSP.shiftDataRight(newDataY);
    // No shift otherwise

    myLSP.mergeTreefromSnakeBox();      // Recompute the merge tree (if desired)

    waitcnt=waitdelay;            // Allow shifts to be delayed by waitdelay number of frames for autoshift applications
    tidx = tidx+1;
  }

  if(autoshift==true)            // Lower the wait count if auto-shifting, at 0 it triggers s shift.
    waitcnt = waitcnt-1;

  if(isPlaying)                  // Are we playing live audio?
    playAudioData();             // Feed the web audio at visual rates (yes this is weird!)
}

function draw_slide1(p5)
{
  console.log("Drawing slide 1");
  draw_slide(p5);
}

function draw_slide2(p5)
{
  console.log("Drawing slide 2");
  draw_slide(p5);
}

// p5 mouse move callback
function mouseMoved_generic(p5,evt)
{
  let y = p5.mouseY;
  if(isNaN(y)) return;

  levelset = (y-innerh/2);//200;          // Allow mouse steering of the level used for level set displays
  if(levelset > 190) levelset = 190;
  if(levelset < -190) levelset = -190;
  print(levelset+" "+y);
}

function mouseMoved_slides(p5,evt)
{
  if(p5.isLooping()==true && p5.myCanvas)
  {
    let y = p5.mouseY;

    levelset = (y-innerh/2);//200;
  }
}

let showsplit = false;  
let doshift = - 1;
let waitdelay = 7;
let waitcnt = waitdelay;
let autoshift = false;
let tidx = 0;

let leftdata=[];        // If data is split by surgery contains the left part of the data
let rightdata=[];       // ... the right part of the data

// Piecewise-linear deformation performed on all snake boxes
// Input(s):  px   .. 0-1 noramlized x position inside a box (0 left, 1 right)
//            py   .. 0-1 normalized y position inside a box (0 bottom, 1 top)
// Output(s): dataY  .. Content underlying monotones has been deformed.
function deformAllBoxSnakes(px, py)
{
  print("px " + px + " py " + py); // Computed px and py are normalized positions inside a rectangle hence can be applied to any snake box.

  for (let i = 0; i < myLSP.boxsnake.length; i++)
  {
    if (myLSP.boxsnake[i].ext == false)
    {
      if (domirror == false || myLSP.boxsnake[i].dir > 0)          // domirror decides how ascending and descending monotones are handled. If domirror is true, then it mirrors the coordinates with different directions.
        linearDeform(i, myLSP.boxsnake[i].sx + px * (myLSP.boxsnake[i].ex - myLSP.boxsnake[i].sx), myLSP.boxsnake[i].sy + py * (myLSP.boxsnake[i].ey - myLSP.boxsnake[i].sy));
      else
        linearDeform(i, myLSP.boxsnake[i].sx + (1 - px) * (myLSP.boxsnake[i].ex - myLSP.boxsnake[i].sx), myLSP.boxsnake[i].sy + (1 - py) * (myLSP.boxsnake[i].ey - myLSP.boxsnake[i].sy));
    }
  }
}

// linear interpolation (to avoid needing to interface p5 who offers an equivalent)
const lerp = (x, y, i) => x * (1 - i) + y * i;

// Compute a one-point piecewise linear interpolation within a given box snake rectangle.
// currentbox is a given box snake ractangle.
// xpos is the x position of the linear interpolation point.
// relypos is the y position of the piecewise interpolation position.
//
function linearDeform(currentbox,xpos,relypos)
{
  let p = myLSP.dataY.length;
  let crect = myLSP.boxsnake[currentbox];
  let xposl=Math.round(xpos);
  if(Math.round(xpos)-crect.sx<0)
  {
    print("min "+(Math.round(xpos)-crect.sx));
    xposl = crect.sx;
  }
  if(Math.round(xpos)-crect.ex>0)
  {
    print("max "+(Math.round(xpos)-crect.ex));
    xposl = crect.ex;
  }
  if(isNaN(xposl)||isNaN(xpos)||!isFinite(xposl)||!isFinite(xpos))
  {
    print("WatMan");
    return;
  }

  if(outofrectedits)
  {
    if(crect.sy>crect.ey)
    {
      relypos = Math.min(relypos,crect.sy);
      relypos = Math.max(relypos,crect.ey);
    }
    else
    {
      relypos = Math.max(relypos,crect.sy);
      relypos = Math.min(relypos,crect.ey);
    }
  }
  if((relypos-crect.sy)*(crect.ey-relypos)>=0) // Check bounds via determinant
  {
    for(let i=crect.sx;i<=xposl;i++)
    {
      myLSP.dataY[i.mod(p)]=lerp(crect.sy,relypos,(i+1-crect.sx)/(xposl-crect.sx+1));
    }
    for(let i=xposl+1;i<=crect.ex;i++)
    {
      myLSP.dataY[i.mod(p)]=lerp(relypos,crect.ey,(i-(xposl+1)+1)/(crect.ex-xposl+1));
    }
  }
  else
    print("pp: "+(relypos-crect.sy)*(crect.ey-relypos)+" "+(relypos-crect.sy)+" "+(crect.ey-relypos)+" "+relypos+" "+crect.sy+" "+crect.ey);
}




// p5 mouse pressed callback
// We use mouse pressed mouse movement to get 2-d coordinate within a snake box for deformation.
// Compare Essl, G. "Topology-Preserving Deformations of Digital Audio" DAFx 2024, we use piecewise linear deformation.
// lastpx, lastpy contains normalized deformation positions for use in streaming deformations.
let lastxpos = 0;
let lastypos = 0;
let domirror = true;
let lastpx, lastpy;
function mousePressed_generic(p5) {

  if (p5.mouseY > totalh) return;

  let xpos = (p5.mouseX - leftmargin) / innerw * (myLSP.dataY.length - 1);
  lastypos = p5.mouseY;

  let relypos = -(p5.mouseY - innerh / 2);

  let currentbox = myLSP.findbox(xpos);

  if (currentbox == -1)
    return;

  lastxpos = xpos;

  let p = myLSP.dataY.length;
  let px, py;
  let ymax = Math.max.apply(null, myLSP.dataY.map(Math.abs));

  print('ym ' + ymax);

  if (myLSP.betti1 == 0 && currentbox == highlightbox && xpos >= 0 && myLSP.boxsnake[currentbox].ext == false) {
    if (globaledit == true) {                 // Global edit means that we deform all snake boxes, not just the one currently selected
      print("GE " + currentbox + " " + highlightbox);
      if (myLSP.boxsnake[currentbox].ex - myLSP.boxsnake[currentbox].sx != 0) {
        px = (xpos - myLSP.boxsnake[currentbox].sx) / (myLSP.boxsnake[currentbox].ex - myLSP.boxsnake[currentbox].sx);
        py = (relypos / normalizer * ymax - myLSP.boxsnake[currentbox].sy) / (myLSP.boxsnake[currentbox].ey - myLSP.boxsnake[currentbox].sy);
      }
      else {
        px = 0;
        py = (relypos - myLSP.boxsnake[currentbox].sy) / (myLSP.boxsnake[currentbox].ey - myLSP.boxsnake[currentbox].sy);
      }

      if (myLSP.boxsnake[currentbox].dir < 0 && domirror == true) {         // Are we using direction of monotone? Yes? Mirror the coordinates.
        py = 1 - py;
        px = 1 - px;
      }
      deformAllBoxSnakes(px,py);
      lastpx = px;
      lastpy = py;
    }
    else        // No global edit? Fine we just deform inside the current one.
      linearDeform(currentbox, xpos, relypos, p, p5);

  }
  highlightbox = currentbox;       // Given we clicked inside a rectangle area of a box, make it the currently highlighted one
}

// p5 keypressed callback
function keyPressed_generic(p5)
{
  print("KEY: "+p5.key)
  if(p5.key=='F' || p5.key=='f')      // F key selects frequency transformed data via FFT. Data must be powers of 2.
    {
      if(myLSP.dataY==fdataY)           // Already have active frequency domain data? Do nothing.
        return;

      const myFFT = new FFT(myLSP.dataY.length);

      var ip = tdataY;
        ip = tdataY.map((element) => element / normalizer);
      var op = myFFT.createComplexArray(); 
      myFFT.transform(op,myFFT.toComplexArray(ip));
      fftout = op;
      myFFT.fromComplexArrayImg(op,fdataP);
      print("fdp: "+fdataP.length);
      print("fdata: " +fdataP);
      let op2 = new Array(myLSP.dataY.length);
      myFFT.fromComplexArray(op,op2);
      console.log(op2.length);
      print("DATA "+op2);
      tdataY = myLSP.dataY;
//      var fnormalizer = ParsevalSum(op2);
      fdataY = op2.map((element) => element *normalizer);
      print(fdataY.length);
      myLSP.dataY = fdataY;

      // Transformed data is new data, so we have to compute everything for it.
//      myLSP.computePH();
      myLSP.computeSnakeBoxes();
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
    }
  if(p5.key =='T' || p5.key =='t')      // T key selects time domain via inverse FFT. Data must be powers of 2.
    { 
      if(myLSP.dataY == tdataY)
        return;

      print("IFFT");
      const myFFT = new FFT(myLSP.dataY.length);

      const out = myFFT.createComplexArray();
      ip = Array.from(fdataY);
      ip = ip.map((element) => element / normalizer);

      let data = myFFT.combineComplexArray(ip,fdataP);
      print("data: "+data);
      print("fffo: "+ fftout);
      myFFT.inverseTransform(out,data); 
      p5.print("out: "+out);
      tdataY = myFFT.fromComplexArray(out);
      print(tdataY.length);
      tdataY = tdataY.map((element) => element * normalizer);
      print(tdataY);
      
      myLSP.dataY = tdataY;
//      myLSP.computePH();
      myLSP.computeSnakeBoxes();
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
    }
  if(p5.key == ' ' && shiftkeys==true)     // space bar does a single step shift
  {
    if(!showsplit)
      waitcnt = 0;
  }
  if(p5.key == 'G' || p5.key == 'g')      // Toggle between global and local deformations
  {
    console.log("GE "+globaledit);
    globaledit = !globaledit;
  }
  if(p5.key == 'J' || p5.key == 'j')      // Toggle mirror deformations 
  {
    domirror = !domirror;
  }
  if(p5.key == 'Q' || p5.key == 'q')      // Live detuning of an iterative oscillator (up)
  {
    fmomega = fmomega*1.25;
    console.log(fmomega);
  }
  if(p5.key == 'R' || p5.key == 'r')      // Live detuning of an iterative oscillator (down)
  {
    fmomega = fmomega/1.25;
    console.log(fmomega);
  }
  if(p5.key == 'P' || p5.key == '\\' || p5.key == 'p')      // Toggle live audio playback vie web audio worklets
  {
    if(tdataY.length==0)
      tdataY = myLSP.dataY;
    if(myLSP.dataY==fdataY)
      freqtotime();           // We have to play back in the time domain, so if our data is in the frequency domain it needs to be transformed back

    if(currentindex == cbufferindex)
      dostreaming = true;
    console.log(currentindex+" "+cbufferindex+" "+p5.currentfunc);

    if(!isPlaying)
    {
      isPlaying = true;
      playAudioBufferStream();
    }
    else
    {
      isPlaying = false;
      stopAudioBufferStream();
      dcnt=0; 
      if(dostreaming==true)
        myLSP.computeBarcode();
      dostreaming = false;
    }
  }
  if(p5.key == 'C' || p5.key == 'c')         // Toggle between linear and circular domain (via surgery)
  {
    if(usecircular==true)
    {
      console.log("CP1: DECIRCLE");
      splitpoint = myLSP.dataY.length-1;
      myLSP.splitBoxes(myLSP.dataY.length-1); // Decircularize
//        barcode = getBarcodefromRectangles(rectangles);
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
      return;
    }
    else
    {
      console.log("CP1: RECIRCLE");
      myLSP.boxsnake = myLSP.mergeBoxes(myLSP.boxsnake,myLSP.boxsnake);
//        barcode = getBarcodefromRectangles(rectangles);
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
      usecircular = true;
      return;
    }
  }
  if(p5.key == 'A' && shiftkeys == true)        // Toggle autoshift
  {
    autoshift = !autoshift;
  }
  if(p5.key == 'U'|| p5.key == 'u')             // Toggle Parameter GUI (slider part not currently working)
  {    
    if(!p5.gui)
    {
      p5.gui = p5.createGui(p5.mySketch);
      p5.gui.addObject(p5.maingraph.paramstates);
      p5.sliderRange(-190, 190, 1);
      p5.gui.addGlobals('levelset');
      console.log("LS: "+levelset);
    }
    else
    {
      p5.gui.toggleVisibility();
//      p5.removeGui(p5.gui);
//      p5.gui = null;
    }
  }
  if(p5.key == 'H' && shiftkeys == true)        // Toggle help text
  {
    p5.maingraph.toggleHelp();
  }
  if(p5.key == 'S' && shiftkeys == true)        // Split or unsplit data
  {
    if(autoshift!=false)
    {
      autoshift=false;
      waitcnt=waitdelay;
    }
    showsplit = !showsplit;

    if(showsplit==true)
    {
      if(usecircular==true)
      {
        print("CSS1");
        myLSP.splitBoxes(myLSP.dataY.length-1); // Decircularize
      }
            
      splitpoint=csplitpoint;
      myLSP.splitBoxes(splitpoint);
      leftdata = myLSP.dataY.slice(0,splitpoint+1);
      rightdata = myLSP.dataY.slice(splitpoint+1,myLSP.dataY.length);
      leftbarcode = getBarcodefromRectangles(leftrectangles);
      rightbarcode = getBarcodefromRectangles(rightrectangles);
      print("LR "+leftdata.length+" "+rightdata.length);
    }
    else
    {
      myLSP.boxsnake = myLSP.mergeBoxes(leftrectangles,rightrectangles);
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
//      barcode = getBarcodefromRectangles(rectangles);
    }
  }
  if(p5.key == '=' || p5.keyCode===187)       // Save an SVG figure of current graph
  {
    if(rendersvg == 1 || savesvg == 1)
    {//filename here
      let splitstate = "merged"+(usecircular?"(circ)":"(lin)");
      if(showsplit)
        splitstate = "split"

      p5.save(dataselectmenu.selected()+"-("+levelset+")+("+defx+"_"+defy+")"+drawrect+label+noiselevel+elderfilename[showelder]+"-"+splitstate+".svg"); // give file name
    }
    print("svg saved");
  }
  if(p5.key =='0')          // Toggle between sublevel and superlevel set
  {
    computesuperlevelset = !computesuperlevelset;
    maingraph.setSuperlevelset(computesuperlevelset);
    myLSP.computeBarcode();
  }
  if(p5.key == 'E' && shiftkeys == true)      // Circle through different barcode computation rules and algorithms
  {
    if(overridemergetreeelder==true)
    {
      print("LOCAL");
      overridemergetreeelder=false;
      showelder=false;
    }
    else if(showelder==true)
    {
        print("MT");
        overridemergetreeelder=true;
    }
    else
      showelder = !showelder;

    myLSP.computeBarcode();
    
    if(overridemergetreeelder==true)
      barcodemode = "ElderMergeTree";       // Elder computation from merge tree
    else if(showelder==true)
      barcodemode = "BARYElder";            // Baryshnikov's (modified) algorithm for elder rule
    else
      barcodemode = "Local";                // Local bar code rule

    console.log(barcodemode);
  }
  if(p5.key == 'M' && p5.key == 'm')        // Construct Barcodes with order reversed (minima vs maxima exchanged)
  {
    mindirorder = -mindirorder;
    print("M "+mindirorder);
    if(showsplit==true)
    {
      p5.maingraph.setMinDirOrder(mindirorder);
      p5.secondgraph.setMinDirOrder(mindirorder);
      leftbarcode = getBarcodefromRectangles(leftrectangles);
      rightbarcode = getBarcodefromRectangles(rightrectangles);
    }
    else
    {
      p5.maingraph.setMinDirOrder(mindirorder);
      myLSP.mergeTreefromSnakeBox();
      myLSP.computeBarcode();
//        barcode = getBarcodefromRectangles(rectangles);
    }
  }
  if(p5.key == 'N')       // Invert data
  {
    invertData();
//    myLSP.computePH();
    myLSP.computeSnakeBoxes();
    myLSP.mergeTreefromSnakeBox();
    myLSP.computeBarcode();
  }
  if(p5.key == 'D' && shiftkeys==true)    // Flip shift direction
  {
    doshift=-doshift;
  }
  print(p5.keyCode);
  if(p5.keyCode===p5.LEFT_ARROW)        // Select highlighted box snake
    {
       highlightbox = (highlightbox - 1).mod(myLSP.boxsnake.length); 
       if(showsplit==true)
       {
        p5.maingraph.setHighlightPos(highlightbox);
        p5.secondgraph.setHighlightPos(highlightbox);
       }
       else
       p5.maingraph.setHighlightPos(highlightbox);
//      print(highlightbox);
    }
  if(p5.keyCode===p5.RIGHT_ARROW)        // Select highlighted box snake
    {
       highlightbox = (highlightbox + 1).mod(myLSP.boxsnake.length); 
//      print(highlightbox);
    }
  if(p5.keyCode===190 || (p5.keyCode===219 && p5.keyIsDown(p5.SHIFT))) // '.' Moves flats sample points between neighboring sname boxes (see Essl DAFx24)
    {
      console.log("Shift-[");
      if(globaledit)
      {
        for(let i=0;i<myLSP.boxsnake.length;i++)
        {
          if(myLSP.boxsnake[i].ext==true) continue;
          highlightbox = i;
          resizeFlatMembershipRightGrow(i);
        }
      }
      else
      resizeFlatMembershipRightGrow(highlightbox);
      
    }
  if(p5.keyCode===188 || (p5.keyCode===221 && p5.keyIsDown(p5.SHIFT))) // ',' Moves flats sample points between neighboring sname boxes (see Essl DAFx24)
    {
      console.log("Shift-]");
      if(globaledit)
        {
        for(let i=0;i<myLSP.boxsnake.length;i++)
        {
          if(myLSP.boxsnake[i].ext==true) continue;
          highlightbox = i;
          resizeFlatMembershipRightShrink(i);
        }
      }
      else
      resizeFlatMembershipRightShrink(highlightbox);
    }
  if(p5.keyCode===219) // '['   Moves flats sample points between neighboring sname boxes (see Essl DAFx24)
    {
      if(globaledit)
        {
        for(let i=0;i<myLSP.boxsnake.length;i++)
        {
          if(myLSP.boxsnake[i].ext==true) continue;
          highlightbox = i;
          resizeFlatMembershipLeftGrow(i);
          resizeFlatMembershipRightGrow(i);
        }
      }
      else
      resizeFlatMembershipLeftGrow(highlightbox);
      
    }
  if(p5.keyCode===221) // ']'   Moves flats sample points between neighboring sname boxes (see Essl DAFx24)
    {
      if(globaledit)
        {
        for(let i=0;i<myLSP.boxsnake.length;i++)
        {
          if(myLSP.boxsnake[i].ext==true) continue;
          highlightbox = i;
          resizeFlatMembershipLeftShrink(i);
          resizeFlatMembershipRightShrink(i);
        }
      }
      else
      resizeFlatMembershipLeftShrink(highlightbox);
    }
}

//
// exported stuff for instancing and use in web pages for slides/posters etc.
//

export const switch_slide1 = function () { console.log("Switching1 "+functionName[startfunc]); forcecopyFunction_f(functionName[startfunc]); }
export const switch_slide2 = function () { console.log("Switching2 "+functionName[startfunc2]); forcecopyFunction_f(functionName[startfunc2]); }

// Create instances for different use cases
export const InstancedSketchGeneric =  function(p5) {
  p5.setup = function () { setup_generic(p5,this); }
  p5.draw = function () { draw_generic(p5); }
  p5.mouseMoved = function (evt) { mouseMoved_generic(p5,evt); }
  p5.mouseDragged = function() { p5.mousePressed(); }
  p5.mousePressed = function () { mousePressed_generic(p5); }
  p5.keyPressed = function () {  keyPressed_generic(p5); }
}

export const InstancedSketchPoster =  function(p5) {
  p5.setup = function () { setup_poster(p5); }
  p5.draw = function () { draw_generic(p5); }
  p5.mouseMoved = function (evt) { mouseMoved_generic(p5,evt); }
  p5.mouseDragged = function() { p5.mousePressed(); }
  p5.mousePressed = function () { mousePressed_generic(p5); }
  p5.keyPressed = function () {  keyPressed_generic(p5); }
}
  

export const InstancedSketchSlide1 =  function(p5) {
  p5.setup = function () { setup_slide1(p5); }
  p5.draw = function () { draw_slide1(p5); }
  p5.mouseMoved = function (evt) { mouseMoved_slides(p5,evt); }
  p5.mouseDragged = function() { p5.mousePressed(); }
  p5.mousePressed = function () { mousePressed_generic(p5); }
//  p5.keyPressed = function () {  keyPressed_generic(p5); }
}

export const InstancedSketchSlide2 =  function(p5) {
  p5.setup = function () { setup_slide2(p5); }
  p5.draw = function () { draw_slide2(p5); }
  p5.mouseMoved = function (evt) { mouseMoved_slides(p5,evt); }
  p5.mouseDragged = function() { p5.mousePressed(); }
  p5.mousePressed = function () { mousePressed_generic(p5); }
  p5.keyPressed = function () {  keyPressed_generic(p5); }
}

//
// Compute Inverse FFT to make frequency domain data available for audio playback
//

function freqtotime()
{
  print("IFFT");
  const myFFT = new FFT(myLSP.dataY.length);

  const out = myFFT.createComplexArray();
  let ip = Array.from(fdataY);
  ip = ip.map((element) => element / normalizer);

  let data = myFFT.combineComplexArray(ip,fdataP);
  myFFT.inverseTransform(out,data);
  tdataY = myFFT.fromComplexArray(out);

  tdataY = tdataY.map((element) => element * normalizer);
  return;
}

//
//  Non-streaming/non-looping legacy audio playback. No longer used.
//

function playAudioBuffer()
{
const audioCtx = new (window.AudioContext || window.webkitAudioContext)();

// Create a mono buffer at the sample rate of the AudioContext
const myArrayBuffer = audioCtx.createBuffer(
    1,
  audioCtx.sampleRate * 1,
  audioCtx.sampleRate,
  );
  const nowBuffering = myArrayBuffer.getChannelData(0);
  for (let i = 0; i < myArrayBuffer.length; i++) {
    nowBuffering[i] = tdataY[i%tdataY.length]/normalizer;
  }
  
  const source = audioCtx.createBufferSource();
  source.buffer = myArrayBuffer;
  source.connect(audioCtx.destination); // Connect to speakers or headphones
  source.start(); // Start playing
}

//
// WebAudio worklet based audio playback
//

async function playAudioBufferStream()
{
  console.log("creating audio context");
  if (!audioContext) {
    try {
      audioContext = await createAudioContext();
    } catch(error) {
      // Failed to create AudioContext (never seen this happen!)
      print("ERROR Couldn't create the AudioContext");
      console.error(error);
      return;
    }
    print("Audio Context created");
  }

  // Resume playback
  audioContext.resume();
  isPlaying = true;
}

function stopAudioBufferStream()
{
  audioContext.suspend();
  isPlaying = false;
}
let ttt=0;
function playAudioData()
{
  if(!audioContext) return;

  if(dostreaming == false)
    playAudioDataLooped();
  else
    playAudioDataStreamed();
}

//
// Play a given buffer looped.
//

function playAudioDataLooped()
{
  if(!audioContext) return;
  print("playing audio buffer = stream(looped) "+dostreaming);
  let realdata = [];


  if(dostreaming == false)
  {
    // This operates on loading audio from a display refresh hence: 44100/60/128=5.741 to 48000/60/128=6.25 depending on the audio rate. There is a check if we fall behind.
    let m = 6;

    if(myLSP.dataY == fdataY)
      freqtotime();

    if(realdataQueue.getAvailableSamples()>6*RENDER_QUANTUM) // Queue has been filled to 6
      m=6;
    else                                                     // Fill a bit more to make sure there are no gaps
    {
      m=7;
    }
    realdata.push(new Float32Array(m*RENDER_QUANTUM));

    for (let i = 0; i < m*RENDER_QUANTUM; i++) {
      realdata[0][i] = tdataY[ttt%tdataY.length]/normalizer;
      ttt++;
    }
    realdataQueue.push(realdata, m*RENDER_QUANTUM);
  }
}

let us=8;
let newDataYStreamed = Array(RENDER_QUANTUM*us);
function playAudioDataStreamed()
{
  print("playing audio buffer = stream(streaming) "+dostreaming);
  if(srealdata.length==0)
    srealdata.push(new Float32Array(RENDER_QUANTUM*us));

  let m=6;
  if(realdataQueue.getAvailableSamples()>6*RENDER_QUANTUM) // Queue has been filled to 6
    m=6;
  else                                                     // Fill a bit more to make sure there are no gaps
  {
    m=8;
  }

  for (let i = 0; i < m*RENDER_QUANTUM/us; i++) {

    for(let i=0; i<RENDER_QUANTUM*us; i++)
      newDataYStreamed[i]= normalizer*incrementFMPhase();

    myLSP.shiftDataLeft(newDataYStreamed);
    deformAllBoxSnakes(lastpx, lastpy);
    dcnt = 1; // Disable display updates for maximum audio performance.
// Comment the above line and uncomment the below two to get interactive display rendering (at a potential webaudio performance cost)    
//    mergeTreefromSnakeBox();   // Compute the merge tree from the box snake
//    computeBarcode();          // Compute bar codes from a selected method

    for (let i = 0; i < RENDER_QUANTUM*us; i++)
    {
      srealdata[0][i] = myLSP.dataY[i]/normalizer;
    }
    realdataQueue.push(srealdata, RENDER_QUANTUM*us);
  }
}

// Plays a single frame, insufficient for our current performance needs, we need to bundle multiple frames.
let srealdata = [];
let ttt2 = 0;
function playAudioFrame()
{
  for (let i = 0; i < RENDER_QUANTUM; i++) {
    srealdata[0][i] = tdataY[i]/normalizer;
    ttt2++;
  //    console.log(realdata[0][i]);
  }
  realdataQueue.push(srealdata, RENDER_QUANTUM);
}
