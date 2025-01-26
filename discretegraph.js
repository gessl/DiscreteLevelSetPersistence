//
// disGraph provides discrete graphing
// Designed to support project on discrete set level set functions, render persistence homology information, merge trees and the like
// Georg Essl (Feburary 2024-January 2025)
//

// This is a hack. Just add c in front of a print to guarantee the debug message. Minimal keystroke hack.
function cprint(a)
{
  console.log(a)
}

// Drawing Functions

class disGraph {
  constructor(p5,tw,th,lm,rm) {
    this.p5 = p5;
    this.totalw = tw;
    this.totalh = th;
    this.leftroot = 0;
    this.toproot = 0;
    this.leftmargin = lm;
    this.rightmargin = rm;//0;//20;//200;
    this.bottommargin = 20;
    this.bottomconnect = 20;
//    this.dotsize = 7;
    this.innerw = this.totalw-this.leftmargin/*-this.dotsize*/-this.rightmargin;
    this.innerh = this.totalh-this.bottommargin-this.bottomconnect*2;
    this.marginw = this.totalw-this.innerw;
    this.marginh = this.totalh-this.innerh;
    this.arrowheadspread = 5;
    this.rectstroke = 5;
    this.axisstroke = 3;
    this.levelsetstroke = 5;
    this.linestroke = 4;
    this.impulsestroke = 3;
    this.barcodestroke = 5;
    this.zerolinestroke = 3;
    this.bubblesize = 12;//6;//12;
    this.cursorsize = 10;
    this.arrowheadlen = 9;

    // Number of data points in the time series (for layouting)
    this.numPts = 0;
    // Normalize data to allowed maximum
    this.normalizer = 180;
    // Highlight position
    this.highlightbox = 1;
    // Bar positioning
    this.barpos = 0;
    this.baroffs = 10;
    this.barmargin = 40;
    // Visibility states
    this.paramstates =
    {
      drawlinegraph: false,
      drawalllines: false,
      drawrect: true,
      drawmonotoneonly: false,
      showhighlight: false,
      drawsublevelgraph: true,
      showtriset: true,
      drawlinelevel: true,
      drawsetoflevels: false,
      drawbarcode: true,
      drawbarcodecount: false,
      showsplitpoint: false,
      showleveldots: false,
      drawdots: true,
      drawimpulses: true,
      dotsubsample: 1,
      dotsubsampleMin: 1,
      dotsubsampleMax: 16,
      dotsubsampleStep: 1,
      drawmergetree: true
    };
    this.computesuperlevelset=false;
    this.showcursor = false;

    this.showdeform = false;

    this.drawextremaarrow = false;
    this.drawaxis=true;
    this.drawdotlines=false;

    this.debugrectnumbers = false;
    this.showhelp = false;

    this.donormalize = false;
    this.showsplitline = false;
  }
  clone() {
    let newgraph = new disGraph(this.p5,this.totalw,this.totalh,this.leftmargin,this.rightmargin);
    newgraph.showhelp = false;
    return newgraph;
  }
  toggleHelp(){
    this.showhelp = !this.showhelp;
  }
  setSuperlevelset(sl)
  {
    this.computesuperlevelset = sl;
  }
  setBubbleSize(bs)
  {
    this.bubblesize=bs;
  }
  setMinDirOrder(dir)
  {
    this.mindirorder = dir;
  //  print("mdo: "+this.mindirorder);
  }
  setDrawLineLevel(drawlinelevel)
  {
    this.paramstates.drawlinelevel = drawlinelevel;
  }
  setDrawSubLevelSet(drawsublevelgraph)
  {
    this.paramstates.drawsublevelgraph = drawsublevelgraph;   
  }
  setDrawRect(sr)
  {
    this.paramstates.drawrect=sr;
  }
  setSize(tw,th,lm,rm)
  {
    this.totalw = tw;
    this.totalh = th;
    this.leftmargin = lm;
    this.rightmargin = rm;
    this.innerw = this.totalw-this.leftmargin/*-this.dotsize*/-this.rightmargin;
    this.innerh = this.totalh-this.bottommargin-this.bottomconnect*2;
    this.marginw = this.totalw-this.innerw;
    this.marginh = this.totalh-this.innerh;
  }
  setRootPos(leftroot,toproot)
  {
    this.leftroot = leftroot;
    this.toproot = toproot;
  }
  setAllData(dataY,rect,mtree,barcode,setoflevels,xpert,usecircular,basepoint)
  {
    this.dataY = dataY;
    this.rectangles = rect;
    this.mergetree = mtree;
    this.barcode = barcode;
    this.setoflevels = setoflevels;
    this.xPert = xpert;
    this.usecircular = usecircular;
    this.numPts = this.dataY.length;
    this.bp = basepoint;
  //  print("BP "+this.bp);
  }
  setHighlightPos(pos)
  {
    this.highlightbox = pos%this.rectangles.length;
  }
  // Draw an arrowhead
  arrowhead(x,y,angle) {
    this.p5.push();
    this.p5.translate(x,y);
    this.p5.rotate(angle)
    this.p5.strokeWeight(this.axisstroke);
    this.p5.strokeJoin(this.p5.MITER);
    this.p5.noFill();
    this.p5.stroke(0);
    this.p5.beginShape();
    this.p5.vertex(-this.arrowheadlen, this.arrowheadspread);
    this.p5.vertex(0, 0);
    this.p5.vertex(-this.arrowheadlen, -this.arrowheadspread);
    this.p5.endShape();
    this.p5.pop();
  }
    
  // Draw the line at zero
  drawzeroline()
  {
  //    if(this.paramstates.drawsetoflevels==true) return;
    
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin/2+this.axisstroke,this.toproot+this.innerh/2);
    this.p5.strokeWeight(this.zerolinestroke);
    this.p5.stroke(0,0,0,128);
    this.p5.line(0,0,this.innerw+this.leftmargin/2,0);
    this.p5.pop();
  }

  // Draw the horizontal line at a given level
  drawlevelline(ly)
  {
    if(this.paramstates.drawlinelevel==false) return;
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin/2+this.axisstroke,this.toproot+this.innerh/2);
    this.p5.strokeWeight(this.levelsetstroke);
    this.p5.stroke(255,0,0,128);
    this.p5.line(0,ly,this.innerw+this.leftmargin/2,ly);
    this.p5.pop();
  }

  // Draw Y axis
  drawyaxis()
  {
    this.p5.push();
    this.p5.translate(this.leftroot,this.toproot);
    this.p5.strokeWeight(this.axisstroke);
    this.p5.line(this.leftmargin/2,0,this.leftmargin/2,this.bottommargin/2+this.innerh);
    this.arrowhead(this.leftmargin/2.0,0+this.axisstroke,-Math.PI/2);
    this.p5.pop();
  }

  // Draw X axis
  drawxaxis()
  {
    this.p5.push();
    this.p5.translate(this.leftroot,this.toproot);
    this.p5.strokeWeight(this.axisstroke);
    this.p5.line(this.leftmargin/2,this.bottommargin/2+this.innerh,this.leftmargin+this.innerw,this.bottommargin/2+this.innerh);
    this.arrowhead(this.leftmargin+this.innerw-this.axisstroke,this.innerh+this.bottommargin/2,0);
    this.p5.pop();    
  }

  setLineDash(list) {
    this.p5.drawingContext.setLineDash(list);
  }

  drawSetofLevels()
  {
    if(this.paramstates.drawsetoflevels==false) return;
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin/2+this.axisstroke,this.toproot+this.innerh/2);
    for(let i=0;i<this.setoflevels.length;i++)
    {
      this.p5.strokeWeight(this.impulsestroke);
      this.p5.stroke(96,96,96,128);
  //    setLineDash([10, 10]);
  this.p5.line(0,-this.setoflevels[i],this.innerw+this.leftmargin,-this.setoflevels[i]);
    }
    this.p5.stroke(0);
    for(let i=0;i<this.setoflevels.length;i++)
    {
          this.p5.fill(0);
          this.p5.noStroke();
          this.p5.ellipse(this.leftmargin+this.innerw, -this.setoflevels[i], this.bubblesize);
          if(this.setoflevels.length-1 > i)
            {
              this.p5.stroke(0);
              this.p5.strokeWeight(this.levelsetstroke);
              this.p5.line(this.leftmargin+this.innerw, -this.setoflevels[i],this.leftmargin+this.innerw,-this.setoflevels[i+1])
            }
    }  
    this.p5.pop();
  }

  // Draw barcode output in Barychnikov's stack order (elder bar is last, order is related to whether local minima are decreasing or increasing)
  drawBarcodes() {
    if(this.paramstates.drawbarcode==false) return;
    
    if(this.barcode==null || this.barcode.length==0)
      return;
    
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw+this.barmargin,this.toproot+this.innerh/2);

    this.baroffs = (this.totalw - (this.leftmargin+this.innerw+2*this.barmargin))/this.barcode.length;
    if(this.baroffs > 10) this.baroffs = 10;
    
    for(let i=0;i<this.barcode.length; i++)
    {  
        this.p5.stroke(0);
        this.p5.strokeWeight(this.barcodestroke);
        if(this.barcode[i][0] && this.barcode[i][1])
          this.p5.line(this.barpos,-this.barcode[i][0][2]*180/this.normalizer,this.barpos,-this.barcode[i][1][2]*180/this.normalizer);
        this.barpos = this.barpos + this.baroffs;
    }
    if(this.paramstates.drawbarcodecount==true)
    {
      this.p5.strokeWeight(1);
      this.p5.textSize(18);
      let str = this.barcode.length;
      if(this.mindirorder == 1)
        str = "v"+str;
      else
        str = "^"+str;

      this.p5.text(str, 0/*this.baroffs*(this.barcode.length-1)/2*/, this.innerh/2+this.bottommargin/2);
    }
    this.p5.pop();
    this.barpos = 0;
  //  print("Number of barcodes: "+barcode.length)
  }

  // Draw blobs for time series data point positions.
  drawEllipses() {
    if(!this.paramstates.drawdots)
      return;
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh/2);
    this.p5.noStroke();
    // draw ellipses
    this.p5.fill(0);
    for (let i = 0; i < this.dataY.length; i=i+this.paramstates.dotsubsample) {
      let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
      let y = this.dataY[i];
      if(this.paramstates.showsplitpoint && (i==this.splitpoint%this.dataY.length || i==(this.splitpoint+1)%this.dataY.length))
        this.p5.fill(255,0,0);
      else
        this.p5.fill(0);
      if(this.showsplitline && (i==this.splitpoint%this.dataY.length && i+1==(this.splitpoint+1)%this.dataY.length))
      {
        this.setLineDash([10, 10]);
        this.p5.stroke(0,0,0,128);
        let xmid = (x+((i+1) * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i+1]))/2;
        this.p5.line(xmid,20,xmid,-200);
        this.setLineDash([]);
      }
      this.p5.ellipse(x, -y*180/this.normalizer, this.bubblesize);
      if(this.drawdotlines==true)
      {
        this.p5.stroke(0,0,0,128);
        this.p5.line(x,-y, this.leftmargin+this.innerw,-y);
        this.p5.noStroke();
      }
    }
    this.p5.pop();
  }

  // Draw data stems for time series data.
  drawimpulsgraph()
  {
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh/2);
    this.p5.strokeWeight(this.impulsestroke);
    this.p5.stroke(64,64,64,128);
//    this.p5.stroke(128,128,128,64);
    // draw lines
//    print("iw "+this.innerw+" "+this.numPts+" "+this.xPert[0]);
//    for (let i = 0; i < this.dataY.length; i++) {
    for (let i = 0; i < this.dataY.length; i=i+this.paramstates.dotsubsample) {
        let x = i * (this.innerw/(this.numPts+1)) + 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
      let y = this.dataY[i];
      this.p5.line(x,0, x, -y*180/this.normalizer);
    }
    this.p5.pop();
  }

  // Draw current sublevel set at a given level. 
  drawsublevelset(ylevel)
  {
    if(this.paramstates.drawsublevelgraph == false) return;
    this.p5.push();
//    this.p5.translate(this.leftroot+this.innerw/(this.numPts+1),this.toproot);
    let offy = this.bottomconnect/2;
    if(this.paramstates.showtriset==true)
      offy = this.bottomconnect+this.bottomconnect/2;
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh+this.bottommargin+offy);
    let lasti = -2; // Invalid number to make sure connectivity check fails until initialized.
    
    for (let i = 0; i < this.dataY.length; i++) {
        if(this.dataY[i] < ylevel || (this.paramstates.showtriset==false && this.dataY[i] == ylevel))
        {
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          let y = this.dataY[i];
          this.p5.fill(0);
          this.p5.noStroke();
          this.p5.ellipse(x, 0, this.bubblesize);
          if(lasti == i-1)
            {
              this.p5.stroke(0);
              this.p5.strokeWeight(this.levelsetstroke);
              this.p5.line( x, 0, (i-1) * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i-1],0);
            }
          lasti = i;
        }
        else if(this.showleveldots)
        {
          this.p5.fill(0);
          this.p5.noStroke();
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          this.p5.ellipse(x, 0, this.bubblesize/4);
        }
      }
    if(this.usecircular == true && lasti == this.dataY.length-1)
      {
        if(this.dataY[0]< ylevel)
          {
            let x = lasti * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[lasti];
            this.p5.line(x, 0, x+(this.innerw / (this.numPts+1))/2, 0);
            this.p5.line(0, 0, 0-(this.innerw / (this.numPts+1))/2, 0);
          }
      }
      this.p5.pop();
  }

  // Draw current sublevel set at a given level. 
  drawsuperlevelset(ylevel)
  {
    if(this.drawsublevelgraph == false) return;
    this.p5.push();
//    this.p5.translate(this.leftroot,this.toproot);
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh+this.bottommargin+(this.bottomconnect/2));
    let lasti = -2; // Invalid number to make sure connectivity check fails until initialized.
    
    for (let i = 0; i < this.dataY.length; i++) {
        if(this.dataY[i] > ylevel)
        {
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          this.p5.fill(0);
          this.p5.noStroke();
          this.p5.ellipse(x, 0, this.bubblesize);
          if(lasti == i-1)
            {
              this.p5.stroke(0);
              this.p5.strokeWeight(this.levelsetstroke);
              this.p5.line(x, 0,  (i-1) * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i-1],0);
            }
          lasti = i;
        }
        else if(this.paramstates.showleveldots)
        {
          this.p5.fill(0);
          this.p5.noStroke();
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          this.p5.ellipse(x, this.innerh+this.bottommargin+(this.bottomconnect/2), this.bubblesize/4);
        }
      }


    if(this.usecircular == true && lasti == this.dataY.length-1)
      {
        if(this.dataY[0]> ylevel)
          {
            let x = lasti * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[lasti];
            this.p5.line(x, 0, x+(this.innerw / (this.numPts+1))/2,0);
            this.p5.line(0, 0, 0-(this.innerw / (this.numPts+1))/2,0);
          }
      }
      this.p5.pop();
  }

  // Draw current sublevel set at a given level. 
  drawatlevelset(ylevel)
  {
    if(this.paramstates.drawsublevelgraph == false) return;
    let lasti = -2; // Invalid number to make sure connectivity check fails until initialized.
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh+this.bottommargin+this.bottomconnect);
    
    for (let i = 0; i < this.dataY.length; i++) {
        if(this.dataY[i] == ylevel)
        {
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          this.p5.fill(0);
          this.p5.noStroke();
          this.p5.ellipse(x, 0, this.bubblesize);
          if(lasti == i-1)
            {
              this.p5.stroke(0);
              this.p5.strokeWeight(this.levelsetstroke);
              this.p5.line(x, 0, (i-1) * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i-1],0);
            }
          lasti = i;
        }
        else if(this.showleveldots)
        {
          this.p5.fill(0);
          this.p5.noStroke();
          let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          let y = this.dataY[i];
          this.p5.ellipse(x, 0, this.bubblesize/4);
        }
      }

    if((this.usecircular == true) && lasti == (this.dataY.length-1))
      {
        if(this.dataY[0] == ylevel)
          {
            let x = lasti * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[lasti];
            this.p5.stroke(0);
            this.p5.strokeWeight(this.levelsetstroke);
            this.p5.line(x, 0, x+(this.innerw / (this.numPts+1))/2,0);
            this.p5.line(0, 0, 0-(this.innerw / (this.numPts+1))/2,0);
          }
      }

      this.p5.pop();

  }


  // Draw piecewise linear connection between sample points. This should be understood to merely represent connectivity and not a metric embedding. I.e. this is perhaps best thought of "up to homotopy".
  drawLines() {
    if(this.paramstates.drawlinegraph == false) return;
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh/2);
    this.p5.strokeWeight(this.linestroke);
    this.p5.stroke(0,192,0,128);
//    this.p5.stroke(32,32,32,255);
    // draw lines
    let px = 0;
    let py = this.dataY[0];
    for (let i = 0; i < this.dataY.length; i++) {
      let x = i * (this.innerw / (this.numPts+1))+ 0.5*this.innerw/(this.numPts+1)*this.xPert[i];
      let y = this.dataY[i];
      if(this.paramstates.drawalllines == true || (py<=-this.levelset && y<=-this.levelset))
        this.p5.line(px, -py*180/this.normalizer, x, -y*180/this.normalizer);

      //store the last position
      px = x;
      py = y;
    }
    this.p5.pop();
  }

  // Draw a rectanglular box even if it "wraps around" due to being data on a circular domain
  // Notice the current implementation disregards embedding perturbations via xpert. If you really need this just add the offets.
  rectMod(sx,sy,ex,ey,p)
  {
    ex = ex.mod(p);
    sx = sx.mod(p);
    if(ex<sx)
      {
        this.p5.line(sx*(this.innerw / (this.numPts+1)), -sy*180/this.normalizer, (p)*(this.innerw / (this.numPts+1)), -sy*180/this.normalizer);
        this.p5.line(sx*(this.innerw / (this.numPts+1)), -ey*180/this.normalizer, (p)*(this.innerw / (this.numPts+1)), -ey*180/this.normalizer);
        this.p5.line(sx*(this.innerw / (this.numPts+1)), -sy*180/this.normalizer, sx*(this.innerw / (this.numPts+1)),    -ey*180/this.normalizer);
        this.p5.line(0*(this.innerw / (this.numPts+1)),  -sy*180/this.normalizer, (ex+1)*(this.innerw / (this.numPts+1)),-sy*180/this.normalizer);
        this.p5.line(0*(this.innerw / (this.numPts+1)),  -ey*180/this.normalizer, (ex+1)*(this.innerw / (this.numPts+1)),-ey*180/this.normalizer);
        this.p5.line((ex+1)*(this.innerw / (this.numPts+1)),-sy*180/this.normalizer,(ex+1)*(this.innerw / (this.numPts+1)),-ey*180/this.normalizer);
      }
    else
      {
        this.p5.rect(sx*(this.innerw / (this.numPts+1)),-sy*180/this.normalizer,(ex+1)*(this.innerw/(this.numPts+1)),-ey*180/this.normalizer);
      }
  }

  drawRectangles()
  {
    if(this.paramstates.drawrect == false) return;
    let fliprect = 1;
    if(this.computesuperlevelset==true)
      fliprect = -1;
    this.p5.push();
    this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1)/2,this.toproot+this.innerh/2);
    this.p5.rectMode(this.p5.CORNERS);
    this.p5.noFill();
    this.p5.strokeWeight(this.rectstroke);

    for(let i=0; i<this.rectangles.length;i++)
      {
        switch(this.rectangles[i].dir)
          {
            case -1:
              if(this.rectangles[i].ext==false)
                this.p5.stroke(0,0,255,128+this.rectangles[i].ext*127);
              else
              this.p5.stroke(255,0,0,128+this.rectangles[i].ext*127);
            break;
            case 1:
              if(this.rectangles[i].ext==false)
                this.p5.stroke(0,255,255,128+this.rectangles[i].ext*127);
              else
              this.p5.stroke(0,255,0,128+this.rectangles[i].ext*127);
              break;
            case 0:
              this.p5.stroke(255,0,255,128);
             break;
          }
        if(i==this.highlightbox && this.paramstates.showhighlight)
          {
  //          print(highlightbox);
            this.p5.stroke(255,0,0,128);
            this.rectMod(this.rectangles[i].sx-this.bp,fliprect*this.rectangles[i].sy,this.rectangles[i].ex-this.bp,fliprect*this.rectangles[i].ey,this.dataY.length);
          }
        else
          if(this.paramstates.drawmonotoneonly == false || this.rectangles[i].ext==false)
            this.rectMod(this.rectangles[i].sx-this.bp,fliprect*this.rectangles[i].sy,this.rectangles[i].ex-this.bp,fliprect*this.rectangles[i].ey,this.dataY.length);

          if(this.drawextremaarrow==true /* && this.rectangles[i].ext==true*/)
          {
//            print("AH "+this.rectangles[i].sx);
            let sx = this.rectangles[i].sx%this.dataY.length;
            this.arrowhead((this.rectangles[i].sx-this.bp+(this.rectangles[i].dx-1)/2)%this.dataY.length*(this.innerw / (this.numPts+1)),-this.rectangles[i].sy*180/this.normalizer-this.rectangles[i].dir*this.bubblesize*1.5,-this.rectangles[i].dir*this.p5.PI/2);
          }
        //      rect(rectangles[i].sx*(innerw / (numPts))-innerw / (numPts)/2,-rectangles[i].sy,rectangles[i].ex*(innerw / (numPts))+innerw / (numPts)/2,-rectangles[i].ey);
        if(this.debugrectnumbers==true)
        {
          this.p5.strokeWeight(1);
          this.p5.textSize(18);
        let tstr='';
        let p=this.dataY.length;
        if(this.rectangles[i].ext==true) tstr = 'X';
        this.p5.text(i+tstr,((this.rectangles[i].sx)%p)*(this.innerw / (this.numPts+1))+(this.rectangles[i].dx-1)*0.5*(this.innerw / (this.numPts+1))-8,-32);
        this.p5.strokeWeight(this.rectstroke);
        }
      }
      this.p5.pop();
  }

//let leftroot = 0;
//let toproot = 0;
plotfullMergeTree(tree)
{
  if(tree==null || this.paramstates.drawmergetree==false) return;
  this.p5.push();
//  this.p5.translate(/*leftroot+*/this.leftmargin/*+innerw*/,/*toproot+*/this.innerh/2);
  this.p5.translate(this.leftroot+this.leftmargin+this.innerw/(this.numPts+1),this.toproot+this.innerh/2);
  this.p5.strokeWeight(this.linestroke);
  this.p5.stroke(0,192,0,128);
  this.plotMergeTree(tree);
  this.p5.pop();
}
plotMergeTree(tree)
{
  let fliptree = 1;
  let x,y;
  if(this.computesuperlevelset==true)
    fliptree = -1;
  if(tree.descendants == null) return [tree.x,tree.y];
  for(let i=0; i<tree.descendants.length;i++)
    {
      [x,y] = this.plotMergeTree(tree.descendants[i]);
      if(x!=undefined)
        {
          let x2 = x * (this.innerw / (this.numPts+1))+ 
0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          let xt = tree.x * (this.innerw / (this.numPts+1))+ 
0.5*this.innerw/(this.numPts+1)*this.xPert[i];
          this.p5.line(xt,-tree.y*fliptree,x2,-y*fliptree);
        }
    }
  return [tree.x,tree.y];
}
  color(c)
  {
    this.p5.color(c);
  }

  // Main graph drawing
  drawGraph(levelset,splitpoint)
  {
//    print("DRAWGRAPH");
//    console.trace();
    this.levelset = levelset;
    this.splitpoint = splitpoint;
    this.p5.stroke(0);
    if(this.rectangles.length==1 || !this.donormalize==true)
      this.normalizer = 180;
    else
    this.normalizer = Math.max.apply(null, this.dataY.map(Math.abs));
//    print("Norm: "+this.normalizer);
    if(this.drawaxis==true)
    {
      this.drawyaxis();
      this.drawxaxis();
      this.drawzeroline();
    }
    this.drawSetofLevels();
    this.drawlevelline(levelset*180/this.normalizer);
    if(this.paramstates.drawimpulses==true)
      this.drawimpulsgraph();
    this.drawLines();
    this.drawEllipses();
    if(this.barcode!=null)
    this.drawBarcodes();
    this.drawsublevelset(-levelset);
    if(this.paramstates.showtriset){
      this.drawsuperlevelset(-levelset);
      this.drawatlevelset(-levelset);
    }
    this.drawRectangles();
    this.plotfullMergeTree(this.mergetree);

    this.p5.stroke(255,0,0,255);
    if(this.showcursor)
    {
      this.p5.fill(255,0,0,255);
      this.p5.ellipseMode(CENTER);
      this.p5.ellipse(this.leftmargin+this.lastxpos*(this.innerw/(this.numPts+1)),this.lastypos,this.cursorsize,this.cursorsize);
    }
    if(this.showhelp)
    {
      this.p5.strokeWeight(1);
      this.p5.stroke(0);
      this.p5.fill(0);
      this.p5.textSize(12);
      let str=""+
              "A - Auto-scroll   "+
              "D - Direction   "+
//              "M - Sub/Super   "+
              "N - Negate Function"+
              "0 - Toggle Subleve/Superlevel"+
              "C - Circular/Linear   "+
              "S - Split/Merge  "+
              "P - Audio  "+
              "T/F - Time/Frequency  "+
              "E - Elder/Bary/Local  "+
              "Space - Step  "+
              "[/] (shift) = Grow/Shrink  "+
              "G - Global/Local Deform  "+
//              "= - Save SVG  "+
              "H - Help";

      this.p5.text(str, 2,this.totalh-2);
  
    }
  }
}



