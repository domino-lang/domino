class ProveLemmaUI {
    projectList;
    proveTheoremUi;
    div;
    
    constructor(projectList, proveProofstepUi, lemmaName) {
        this.projectList = projectList;
        this.proveProofstepUi = proveProofstepUi;
        
        let div = document.createElement("div");
        div.innerHTML = lemmaName;
        div.style.display = "inline-block";
        div.classList.add("block-lemma");
        div.classList.add("block-lemma-new");
        this.div = proveProofstepUi.details.querySelector("div").appendChild(div);
    }

    ui(data) {
        switch (data.method) {
        case "println":
            console.log(data);
            break;
        case "start":
            this.div.classList.add("block-lemma-started");
            this.div.classList.remove("block-lemma-new");
            break;
        case "finish":
            this.div.classList.add("block-lemma-finished");
            this.div.classList.remove("block-lemma-started");
            break;
        }
    }
}

class ProveOracleUI {
    projectList;
    proveTheoremUi;
    details;
    
    constructor(projectList, proveProofstepUi, oracleName) {
        this.projectList = projectList;
        this.proveProofstepUi = proveProofstepUi;
        
        let summary = document.createElement("summary");
        summary.innerHTML = oracleName;
        summary.classList.add("domino-ui-new");

        let div = document.createElement("div");
        div.classList.add("container-lemmas");

        let details = document.createElement("details");
        details.appendChild(summary);
        details.appendChild(div);
        details.classList.add("domino-ui");
        
        this.details = proveProofstepUi.details.appendChild(details);
    }

    ui(data) {
        switch (data.method) {
        case "new":
            this.projectList.register_ui(data.new_uuid, new ProveLemmaUI(this.projectList, this, data.extra));
            break;
        case "start":
            this.details.querySelector("summary").classList.add("domino-ui-started");
            this.details.querySelector("summary").classList.remove("domino-ui-new");
            this.details.open = true;
            break;
        case "finish":
            this.details.querySelector("summary").classList.add("domino-ui-finished");
            this.details.querySelector("summary").classList.remove("domino-ui-started");
            this.details.open = false;
            break;
        case "println":
            console.log(data);
            break;
        }
    }
}

class ProveProofstepUI {
    projectList;
    proveTheoremUi;
    details;
    
    constructor(projectList, proveTheoremUi, proofstepName) {
        this.projectList = projectList;
        this.proveTheoremUi = proveTheoremUi;

        let summary = document.createElement("summary");
        summary.innerHTML = proofstepName;
        summary.classList.add("domino-ui-new");

        let details = document.createElement("details");
        details.appendChild(summary);
        details.classList.add("domino-ui");
        this.details = proveTheoremUi.details.appendChild(details);
    }

    ui(data) {
        switch (data.method) {
        case "new":
            this.projectList.register_ui(data.new_uuid, new ProveOracleUI(this.projectList, this, data.extra));
            break;
        case "start":
            this.details.querySelector("summary").classList.add("domino-ui-started");
            this.details.querySelector("summary").classList.remove("domino-ui-new");
            this.details.open = true;
            break;
        case "finish":
            this.details.querySelector("summary").classList.add("domino-ui-finished");
            this.details.querySelector("summary").classList.remove("domino-ui-started");
            this.details.open = false;
            break;
        case "println":
            console.log(data);
            break;
        }
    }
}

class ProveTheoremUI {
    projectList;
    proveUi;
    details;
    
    constructor(projectList, proveUi, theoremName) {
        this.projectList = projectList;
        this.proveUi = proveUi;

        let theorem = proveUi.project.theorems.get(`theorem/${theoremName}.ssp`);
        this.details = theorem.contentelem.querySelector("details");
        this.details.style.display = "block";
    }

    ui(data) {
        switch (data.method) {
        case "new":
            this.projectList.register_ui(data.new_uuid, new ProveProofstepUI(this.projectList, this, data.extra));
            break;
        case "start":
            this.details.querySelector("summary").classList.add("domino-ui-started");
            this.details.querySelector("summary").classList.remove("domino-ui-new");
            this.details.open = true;
            break;
        case "finish":
            this.details.querySelector("summary").classList.add("domino-ui-finished");
            this.details.querySelector("summary").classList.remove("domino-ui-started");
            this.details.open = false;
            break;
        case "println":
            console.log(data);
            break;
        }
    }
}

class ProveUI {
    projectList;
    project;
    
    constructor(projectList, project) {
        this.projectList = projectList;
        this.project = project;
    }
    
    ui(data) {
        switch (data.method) {
        case "new":
            this.projectList.register_ui(data.new_uuid, new ProveTheoremUI(this.projectList, this, data.extra));
            break;
        case "println":
            console.log(data);
            break;
        }
    }
}

export {ProveUI, ProveTheoremUI, ProveProofstepUI, ProveOracleUI, ProveLemmaUI};
