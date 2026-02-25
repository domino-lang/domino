import {ProveUI} from "./dominoui.js";
//import {} from "./domino-worker.js";

const dominoWorker = new Worker("domino-worker.js", {type: "module"});
const dominoOutput = document.getElementById("domino_output");
const dominoOutputTemplate = document.getElementById("domino_output_template");
const proofUITemplate = document.getElementById("proof_ui_template");
const logOutput = document.getElementById("log_output");

class FilesContainer {
    parent;
    #tabelem;
    typedetail;

    constructor(parent, sort, data) {
        this.parent = parent;

        let tabelem = document.createElement("a");
        let template = document.getElementById("type-detail-template");
        let clone = document.importNode(template.content, true);

        tabelem.innerHTML = sort;
        this.#tabelem = parent.detailnode.querySelector(".project-detail-type-tab").appendChild(tabelem);
        this.typedetail = parent.detailnode.querySelector(".project-detail-type-container").appendChild(clone.children[0]);
        for (const entry of data.data) {
            let tab = document.createElement("a");
            switch (sort) {
            case "Theorems":
                tab.innerHTML = entry.match(/theorem\/([a-zA-Z0-9]*)\.ssp/)[1]
                new TheoremWidget(this, tab, entry);
                break
            case "Games":
                tab.innerHTML = entry.match(/games\/([a-zA-Z0-9]*)\.comp\.ssp/)[1]
                new GameWidget(this, tab, entry);
                break;
            case "Packages":
                tab.innerHTML = entry.match(/packages\/([_a-zA-Z0-9\/]*)\.pkg\.ssp/)[1]
                new PackageWidget(this, tab, entry);
                break;
            }
            tab = this.typedetail.querySelector(".type-detail-file-tab").appendChild(tab);
        }
        this.#tabelem.addEventListener("click", (event) => {
            this.toggle();
        });
    }

    toggle() {
        if (this.typedetail.style.display == "none") {
            this.activate();
        } else {
            this.deactivate();
        }
    }

    deactivate() {
        this.#tabelem.classList.remove("selected");
        this.typedetail.style.display = "none";
    }

    activate() {
        for (const container of this.parent.containers.values()) {
            container.deactivate()
        }
        this.#tabelem.classList.add("selected");
        this.typedetail.style.display = "block";
    }
}

class TheoremWidget {
    #parent;
    #theorem;
    #tab;
    contentelem;

    constructor(parent, tab, data) {
        this.#parent = parent;
        this.#tab = tab;
        this.#theorem = data;

        let template = document.getElementById("theorem-tile-template");
        let clone = document.importNode(template.content, true);

        this.contentelem = parent.typedetail.appendChild(clone.children[0]);
        parent.parent.theorems.set(data, this);

        this.#tab.addEventListener("click", (event) => {
            this.toggle();
        });
        this.contentelem.querySelector("button").addEventListener("click", (event) => {
            this.prove()
        });
    }

    add_proof(proof) {
        const [name, steps] = proof;
        let template = document.getElementById("proof-tile-template");
        let clone = document.importNode(template.content, true).children[0];
        clone.querySelector('h5').innerHTML += name;
        let grid = clone.querySelector(".proof-grid");
        let last;
        for (const step of steps) {
            if (step != last ){
                last = step;
                
                let label = document.createElement("a");
                label.innerHTML = step;
                grid.appendChild(label);

                console.log(this.#parent.parent);
                let svg = new DOMParser().parseFromString(this.#parent.parent.gamegraphs.get(step), 'text/html');
                grid.appendChild(svg.firstChild);
            }
        }

        this.contentelem.appendChild(clone);
    }
    
    prove() {
        let theoremName = this.#theorem.match(/theorem\/([a-zA-Z0-9]*)\.ssp/)[1];
        dominoWorker.postMessage({
            func: "prove",
            project: this.#parent.parent.uuid,
            theorem: theoremName,
        });

    }

    toggle() {
        if (this.contentelem.style.display == "none") {
            this.activate();
        } else {
            this.deactivate();
        }
    }

    deactivate() {
        this.#tab.classList.remove("selected");
        this.contentelem.style.display = "none";
    }

    activate() {
        for (const container of this.#parent.parent.theorems.values()) {
            container.deactivate()
        }
        this.#tab.classList.add("selected");
        this.contentelem.style.display = "block";
    }

}

class GameWidget {
    #parent;
    #game;
    #tab;
    contentelem;

    constructor(parent, tab, data) {
        this.#parent = parent;
        this.#tab = tab;
        this.#game = data;

        let template = document.getElementById("game-tile-template");
        let clone = document.importNode(template.content, true);

        this.contentelem = parent.typedetail.appendChild(clone.children[0]);
        parent.parent.games.set(data, this);

        this.#tab.addEventListener("click", (event) => {
            this.toggle();
        });
    }

    add_graph(svg) {
        this.contentelem.innerHTML += svg;
    }
    
    toggle() {
        if (this.contentelem.style.display == "none") {
            this.activate();
        } else {
            this.deactivate();
        }
    }

    deactivate() {
        this.#tab.classList.remove("selected");
        this.contentelem.style.display = "none";
    }

    activate() {
        for (const container of this.#parent.parent.games.values()) {
            container.deactivate()
        }
        this.#tab.classList.add("selected");
        this.contentelem.style.display = "block";
    }
}

class PackageWidget {
    #parent;
    #pkg;
    #tab;
    contentelem;

    constructor(parent, tab, data) {
        this.#parent = parent;
        this.#tab = tab;
        this.#pkg = data;

        let template = document.getElementById("pkg-tile-template");
        let clone = document.importNode(template.content, true);

        this.contentelem = parent.typedetail.appendChild(clone.children[0]);
        parent.parent.pkgs.set(data, this);

        this.#tab.addEventListener("click", (event) => {
            this.toggle();
        });
        dominoWorker.postMessage({
            func: 'get-package-code',
            project: parent.parent.uuid,
            packagename: data,
        });
    }

    add_code(code) {
        this.contentelem.querySelector('pre').innerHTML = code;
    }
    
    toggle() {
        if (this.contentelem.style.display == "none") {
            this.activate();
        } else {
            this.deactivate();
        }
    }

    deactivate() {
        this.#tab.classList.remove("selected");
        this.contentelem.style.display = "none";
    }

    activate() {
        for (const container of this.#parent.parent.pkgs.values()) {
            container.deactivate()
        }
        this.#tab.classList.add("selected");
        this.contentelem.style.display = "block";
    }
}


class Project {
    constructor(parent, zipfile, astnode) {
        this.zipfile = zipfile;
        this.astnode = astnode;
        this.uuid = crypto.randomUUID();
        this.parent = parent;
        this.containers = new Map();
        this.theorems = new Map();
        this.games = new Map();
        this.pkgs = new Map();

        switch (zipfile.constructor.name) {
        case "File":
            this.name = zipfile.name
            break;
        case "Response":
            let split = zipfile.url.split("/");
            this.name = split[split.length-1];
            break;
        }
        
        let project = this;
        zipfile.arrayBuffer().then(function (bs) {
            dominoWorker.postMessage({
                func: 'load',
                data: new Uint8Array(bs),
                project: project.uuid,
                filename: project.name,
            })
        });
        this.astnode.querySelector("h5").innerHTML = this.name;

        let template = document.getElementById("project-detail-template");
        let clone = document.importNode(template.content, true);
        clone = document.getElementById("document").appendChild(clone.children[0]);
        this.detailnode = clone;
        this.detailnode.querySelector("h2").innerHTML += this.name;

    }

    load_complete(data) {
        this.files = data.data;
        for (const task of ["proofsteps",
                            "list-packages",
                            "list-games",
                            "list-theorems",
                            "projectdetails",
                           ]) {
            dominoWorker.postMessage({
                func: task,
                project: this.uuid,
            });
        }
        this.astnode.addEventListener("click", (event) => {
            const enabled = this.astnode.classList.contains("project-enabled");
            for (const project of this.parent.projects) {
                project.astnode.classList.remove("project-enabled");
                project.detailnode.style.display = "none";
            }
            if (!enabled) {
                this.astnode.classList.add("project-enabled");
                this.detailnode.style.display = "block";
            }
        });
    }

    projectdetails(data) {
        this.gamegraphs = data.data.get("gamegraphs");
        this.theoremdata = data.data.get("theorems");

        for (const [name, graph] of this.gamegraphs.entries()) {
            this.games.get(`games/${name}.comp.ssp`).add_graph(graph);
        }
        for (const [name, proofs] of this.theoremdata.entries()) {
            const theorem = this.theorems.get(`theorem/${name}.ssp`);
            for (const proof of proofs) {
                theorem.add_proof(proof);
            }
        }
    }
    
    list_packages(data) {
        this.containers.set(
            "Packages",
            new FilesContainer(this, "Packages", data)
        );
    }
    package_code(data){
        this.pkgs.get(data.packagename).add_code(data.data);
    }
    list_games(data) {
        this.containers.set(
            "Games",
            new FilesContainer(this, "Games", data)
        );
    }
    list_theorems(data) {
        this.containers.set(
            "Theorems",
            new FilesContainer(this, "Theorems", data)
        );
    }

    ui(data) {
        switch (data.method) {
        case "new": {
            switch (data.sort) {
            case "ProofstepUI":
                projectList.register_ui(data.new_uuid, this);
                break;
            case "ProveUI":
                projectList.register_ui(data.new_uuid, new ProveUI(projectList, this));
                break;
            }            
            break;
        }
        case "proofstep": {
            const loader = this.astnode.querySelector(".loader");
            if (loader) {
                loader.remove();
            }
            this.astnode.querySelector("pre").innerHTML += data.line;
            break;
        }
        }
    }
}

class ProjectList {
    constructor() {
        this.rootElement = document.getElementById("upload-container");
        this.dropZone = document.getElementById("drop-zone");

        this.projects = [];
        this.uis = new Map();
        this.currentProject = -1;
    }

    add_project(zipfile) {
        let template = document.getElementById("project-tile-template");
        let clone = document.importNode(template.content, true);

        clone = this.dropZone.insertAdjacentElement('afterend', clone.children[0]);
        let project = new Project(this, zipfile, clone);
        this.projects.push(project);
        this.uis.set(project.uuid, project);
    }

    get_project(uuid) {
        return this.projects.find((proj) => {return proj.uuid == uuid});
    }

    register_ui(uuid, ui) {
        console.debug("ui registered", uuid, ui);
        this.uis.set(uuid, ui);
    }

    get_ui(uuid) {
        return this.uis.get(uuid);
    }
}


const projectList = new ProjectList();


dominoWorker.onmessage = (e) => {
    console.log(e.data);
    switch (e.data.func) {
    case "load": {
        let project = projectList.get_project(e.data.project);
        project.load_complete(e.data);
        break;
    }
    case "proofsteps": {
        let project = projectList.get_project(e.data.project);
        project.proofsteps(e.data);
        break;
    }
    case "projectdetails": {
        let project = projectList.get_project(e.data.project);
        project.projectdetails(e.data);
        break;
    }
    case "list-packages": {
        let project = projectList.get_project(e.data.project);
        project.list_packages(e.data);
        break;
    }
    case "get-package-code": {
        let project = projectList.get_project(e.data.project);
        project.package_code(e.data);
        break;
    }
    case "list-games": {
        let project = projectList.get_project(e.data.project);
        project.list_games(e.data);
        break;
    }
    case "list-theorems": {
        let project = projectList.get_project(e.data.project);
        project.list_theorems(e.data);
        break;
    }
    case "cvc-solve": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func}`;
        clone.querySelector("pre").innerHTML = e.data.data;
        dominoOutput.appendChild(clone);
        break;
    }
    case "domino-test": {
        const clone = document.importNode(dominoOutputTemplate.content, true);
        clone.querySelector("h5").innerHTML = `${e.data.func}`;
        clone.querySelector("pre").innerHTML = e.data.data;
        dominoOutput.appendChild(clone);
        break;
    }
    case "domino-ui":
        let project = projectList.get_ui(e.data.uuid);
        project.ui(e.data);
        break;
    case "log": {
        const elem = document.createElement("p");
        pelem.innerHTML = e.data;
        logOutput.appendChild(elem);
        break;
    }
    }
}

dominoWorker.onerror = (error) => {
    console.error(error.message);
    console.error(error);
}
console.log(dominoWorker);

let dropZone = document.getElementById("drop-zone");
dropZone.addEventListener("dragover", (e) => {
    e.stopPropagation();
    e.preventDefault();
})
dropZone.addEventListener("drop", (e) => {
    e.stopPropagation();
    e.preventDefault();

    const files = [...e.dataTransfer.items]
          .map((item) => item.getAsFile())
          .filter((file) => file);

    for (const zipfile of files) {
        projectList.add_project(zipfile);
    }
})

let fileUpload = document.getElementById("file-upload");
fileUpload.addEventListener("change", (e) => {
    let zipfile = fileUpload.files[0];
    projectList.add_project(zipfile);
})


let params = new URLSearchParams(window.location.hash.substr(1));
let downloads = params.getAll("load");
setTimeout(() => {
    for (const download of downloads) {
        fetch(download).then((response) => {
            projectList.add_project(response);
        });
    }},
    1000
);
