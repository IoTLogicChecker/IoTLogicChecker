const eternalFormColor = '#4B8F09';
const operationFormColor = '#7B0FF9';
const bindFormColor = '#6F2B30';
const subFormColor = '#5B8FF9';

function preprocess(data){
  data.nodes.forEach(node=>{
    node.label = node.id;
		style = {}
		if (node.eternal){
			style.fill = eternalFormColor;
		}else if(node.operationp){
			style.fill = operationFormColor;
		}else if(node.description.startsWith('bind')){
			style.fill = bindFormColor;
		}
		if(node.available == true){
			node.color = '#55FE66';
		}else{
			node.color = '#FE5566';
		}
		node.style = style
  });
  data.edges.forEach(edge=>{
    if(edge.source == edge.target){
      edge.type = 'loop';
    }
  });
  return data;
}

var layout1 = {
  type:'force',
	center:[450,200],
	preventOverlap:true,
	linkDistance:50,
};

var layout2 ={
	type: 'dagre',
	center:[450,450],
	rankdir: 'LR', // optional
	align: 'DL', //optional 
	nodesep: 20, //optional 
	ranksep: 50, //optional 
	controlPoints: true, // optional
};

const graph = new G6.Graph({
  container: 'container',
	renderer: 'svg',
  width: 900,
  height: 900,
	modes:{
    default:[
      'drag-canvas',
      'drag-node',
      'zoom-canvas',
      {
        type:'tooltip',
        formatText(model){
          return model.description;
        },
      },
    ],
    edit:['click-select'],
  },
  defaultNode: {
    type: 'circle',
    size: [20],
    color: '#5B8FF9',
    style: {
      fill: '#9EC9FF',
      lineWidth: 2,
    },
    labelCfg: {
      style: {
        fill: '#fff',
        fontSize: 7,
      },
    },
  },
  defaultEdge: {
    style: {
      stroke: '#2ef1b0',
			endArrow: true
    }
  },
	layout:layout1,
});

graph.data(preprocess(data));
graph.render();

function EXP(){
	graph.downloadFullImage('test');
}

//setTimeout(()=>{
//	graph.downloadFullImage('test');
//},2000);
