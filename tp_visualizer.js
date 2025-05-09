// === Constants ===
const CELL_HEIGHT = 30;
const CELL_WIDTH = 150;
const TITLE_Y_OFFSET = 40;
const START_X = 50;
const BOX_PADDING = 10;
const BOX_BORDER = 1.5;
const circleRadius = 45;
const groupColors = {
  Mentor: "#FFB6C1", // pink
  Mentee: "#B0E0E6", // blue
};

// === Step 1: Build mappings ===
const listToPerson = new Map();
for (const tuple of person.tuples()) {
  const [listNode, personNode] = tuple.atoms();
  listToPerson.set(listNode.id(), personNode.id());
}

const personToHead = new Map();
for (const tuple of priorities.tuples()) {
  const [_, person, listHead] = tuple.atoms();
  personToHead.set(person.id(), listHead.id());
}

const nextMap = new Map();
for (const tuple of next.tuples()) {
  const [from, to] = tuple.atoms();
  nextMap.set(from.id(), to.id());
}

const matchMap = new Map();
for (const tuple of pair.tuples()) {
  const [_, p1, p2] = tuple.atoms();
  matchMap.set(p1.id(), p2.id());
}

const personToGroup = new Map();
for (const tuple of priorities.tuples()) {
  const [group, person, _] = tuple.atoms();
  personToGroup.set(person.id(), group.id());
}

const allPeople = Person.atoms().map((p) => p.id());

// === Step 2: Clear SVG ===
while (svg.firstChild) svg.removeChild(svg.firstChild);

// === Step 3: Helper function to get preferences
function getPreferenceChainFromListId(headId) {
  const preferences = [];
  const seen = new Set();
  let currentId = headId;

  while (currentId && !seen.has(currentId)) {
    seen.add(currentId);
    const personId = listToPerson.get(currentId);
    if (!personId) break;
    preferences.push(personId);
    currentId = nextMap.get(currentId);
  }

  return preferences;
}

function getGroupColor(personId) {
  const group = personToGroup.get(personId);
  return group?.includes("Mentor") ? groupColors.Mentor : groupColors.Mentee;
}

// === Step 4: Draw preference columns
let col = 0;
let maxBoxHeight = 0;

for (const [personId, headId] of personToHead.entries()) {
  const preferences = getPreferenceChainFromListId(headId);
  const missing = allPeople.filter(
    (p) => p !== personId && !preferences.includes(p)
  );
  // if (missing.length === 1) preferences.push(missing[0]);

  const x = START_X + col * (CELL_WIDTH + BOX_PADDING);
  const boxHeight = (preferences.length + 1) * CELL_HEIGHT + BOX_PADDING;
  maxBoxHeight = Math.max(maxBoxHeight, boxHeight);

  // Background
  const rect = document.createElementNS("http://www.w3.org/2000/svg", "rect");
  rect.setAttribute("x", x - BOX_PADDING / 2);
  rect.setAttribute("y", TITLE_Y_OFFSET - CELL_HEIGHT + 5);
  rect.setAttribute("width", CELL_WIDTH);
  rect.setAttribute("height", boxHeight);
  // rect.setAttribute("fill", "#f0f8ff");
  rect.setAttribute("stroke", "#ccc");
  rect.setAttribute("stroke-width", BOX_BORDER);
  rect.setAttribute("rx", 8);
  rect.setAttribute("ry", 8);
  rect.setAttribute("fill", "#f9f9f9");
  svg.appendChild(rect);

  // Name
  const nameText = document.createElementNS(
    "http://www.w3.org/2000/svg",
    "text"
  );
  nameText.setAttribute("x", x);
  nameText.setAttribute("y", TITLE_Y_OFFSET);
  nameText.textContent = personId;
  nameText.setAttribute("fill", "black");
  nameText.setAttribute("font-size", "16");
  nameText.setAttribute("font-weight", "bold");
  svg.appendChild(nameText);

  function darken(hexColor, amount = 0.5) {
    const num = parseInt(hexColor.replace("#", ""), 16);
    let r = (num >> 16) & 0xff;
    let g = (num >> 8) & 0xff;
    let b = num & 0xff;

    r = Math.floor(r * amount);
    g = Math.floor(g * amount);
    b = Math.floor(b * amount);

    return `rgb(${r}, ${g}, ${b})`;
  }

  // Preferences
  let y = TITLE_Y_OFFSET + CELL_HEIGHT;
  for (const [i, pref] of preferences.entries()) {
    const isMatch = matchMap.get(personId) === pref;

    // Background fill for each preference row
    const prefBg = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "rect"
    );
    prefBg.setAttribute("x", x - 5);
    prefBg.setAttribute("y", y - 20);
    prefBg.setAttribute("width", CELL_WIDTH - 10);
    prefBg.setAttribute("height", 22);
    prefBg.setAttribute("rx", 6);
    prefBg.setAttribute("ry", 6);

    // Set color based on group of the preferred person
    const prefColor = getGroupColor(pref);
    prefBg.setAttribute("fill", isMatch ? darken(prefColor, 0.6) : prefColor);
    svg.appendChild(prefBg);

    const prefText = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "text"
    );
    prefText.setAttribute("x", x);
    prefText.setAttribute("y", y);
    prefText.textContent = `${i + 1}. ${pref}`;
    prefText.setAttribute("fill", isMatch ? "#ffffff" : "black");
    prefText.setAttribute("font-size", "14");
    if (isMatch) prefText.setAttribute("font-weight", "bold");
    svg.appendChild(prefText);

    y += CELL_HEIGHT;
  }

  col += 1;
}

// === Step 5: Draw matched pairs as circles
const shapeStartY = TITLE_Y_OFFSET + maxBoxHeight + 100;
const defs = document.createElementNS("http://www.w3.org/2000/svg", "defs");
defs.innerHTML = `
  <filter id="glow">
    <feDropShadow dx="0" dy="0" stdDeviation="2" flood-color="#aaa"/>
  </filter>
`;
svg.appendChild(defs);

const pairLabel = document.createElementNS(
  "http://www.w3.org/2000/svg",
  "text"
);
pairLabel.setAttribute("x", START_X);
pairLabel.setAttribute("y", shapeStartY - 70);
pairLabel.textContent = "Matched Pairs (Visual):";
pairLabel.setAttribute("fill", "black");
pairLabel.setAttribute("font-size", "16");
pairLabel.setAttribute("font-weight", "bold");
svg.appendChild(pairLabel);

let pairIndex = 0;
const seen = new Set();

for (const [p1, p2] of matchMap.entries()) {
  if (seen.has(p1) || seen.has(p2)) continue;

  const pairSpacing = 250; // or 300 for very large spacing
  const baseX = START_X + pairIndex * pairSpacing;
  //   const baseX = START_X + pairIndex * (CELL_WIDTH + BOX_PADDING);
  const cx1 = baseX + CELL_WIDTH / 5;
  const cx2 = baseX + (4 * CELL_WIDTH) / 4;
  const cy = shapeStartY;

  // Connector line
  const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
  line.setAttribute("x1", cx1 + circleRadius / 2);
  line.setAttribute("y1", cy);
  line.setAttribute("x2", cx2 - circleRadius / 2);
  line.setAttribute("y2", cy);
  line.setAttribute("stroke", "#003366");
  line.setAttribute("stroke-width", "2");
  svg.appendChild(line);

  // Circles
  [
    [p1, cx1],
    [p2, cx2],
  ].forEach(([p, cx]) => {
    const circle = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "circle"
    );
    circle.setAttribute("cx", cx);
    circle.setAttribute("cy", cy);
    circle.setAttribute("r", circleRadius);
    circle.setAttribute("fill", getGroupColor(p));
    circle.setAttribute("stroke", "#003366");
    circle.setAttribute("stroke-width", "1.5");
    circle.setAttribute("filter", "url(#glow)");
    svg.appendChild(circle);

    const label = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "text"
    );
    label.setAttribute("x", cx);
    label.setAttribute("y", cy + 5);
    label.setAttribute("text-anchor", "middle");
    label.setAttribute("font-size", "12");
    label.setAttribute("font-weight", "bold");
    label.textContent = p;
    svg.appendChild(label);
  });

  seen.add(p1);
  seen.add(p2);
  pairIndex += 1;
}

// === Step 6: Draw legend
const legendY = shapeStartY + circleRadius * 2 + 10;

const legendTitle = document.createElementNS(
  "http://www.w3.org/2000/svg",
  "text"
);
legendTitle.setAttribute("x", START_X);
legendTitle.setAttribute("y", legendY - 15);
legendTitle.textContent = "Legend:";
legendTitle.setAttribute("font-size", "13");
legendTitle.setAttribute("font-weight", "bold");
svg.appendChild(legendTitle);

function drawLegendItem(x, y, color, label) {
  const circle = document.createElementNS(
    "http://www.w3.org/2000/svg",
    "circle"
  );
  circle.setAttribute("cx", x + 8);
  circle.setAttribute("cy", y + 5);
  circle.setAttribute("r", 8);
  circle.setAttribute("fill", color);
  circle.setAttribute("stroke", "#333");
  svg.appendChild(circle);

  const text = document.createElementNS("http://www.w3.org/2000/svg", "text");
  text.setAttribute("x", x + 25);
  text.setAttribute("y", y + 9);
  text.textContent = label;
  text.setAttribute("font-size", "12");
  text.setAttribute("fill", "#000");
  svg.appendChild(text);
}

drawLegendItem(START_X, legendY, groupColors.Mentor, "Mentor");
drawLegendItem(START_X + 100, legendY, groupColors.Mentee, "Mentee");

// === Final: Set SVG size
svg.setAttribute("width", START_X + col * (CELL_WIDTH + BOX_PADDING));
svg.setAttribute("height", legendY + 60);

// === Step 7: Display Fairness Metrics ===

function computeRank(p, q) {
  const headId = personToHead.get(p);
  if (!headId) return null;
  const prefs = getPreferenceChainFromListId(headId);
  return prefs.indexOf(q); // 0-based rank = regret
}

function computeGroupDegree(groupName) {
  return Math.max(
    ...allPeople
      .filter((p) => personToGroup.get(p) === groupName)
      .map((p) => computeRank(p, matchMap.get(p)))
  );
}

function computeGroupCost(groupName) {
  console.log(allPeople.filter((p) => personToGroup.get(p) === groupName));
  return allPeople
    .filter((p) => personToGroup.get(p) === groupName)
    .reduce((acc, p) => acc + computeRank(p, matchMap.get(p)), 0);
}

const MentorCost = computeGroupCost("Mentor0");
const MenteeCost = computeGroupCost("Mentee0");
const MentorDegree = computeGroupDegree("Mentor0");
const MenteeDegree = computeGroupDegree("Mentee0");

const totalCost = MentorCost + MenteeCost;
const maxGroupCost = Math.max(MentorCost, MenteeCost);
const groupEqualScore = Math.abs(MentorCost - MenteeCost);
const regretEqualScore = Math.abs(MentorDegree - MenteeDegree);
const maxIndividualRegret = Math.max(MentorDegree, MenteeDegree);

// === Step 7: Display Fairness Metrics (Prettier) ===
const metricsY = legendY + 70;
const metricBoxX = START_X;
const metricBoxWidth = 300;
const metricRowHeight = 24;
const metricPadding = 10;

const metrics = [
  ["Total Cost", totalCost],
  ["Mentor Cost", MentorCost],
  ["Mentee Cost", MenteeCost],
  ["Group Cost Difference (group-equal)", groupEqualScore],
  ["Max Group Cost (balanced)", maxGroupCost],
  ["Max Individual Regret (min-regret)", maxIndividualRegret],
  ["Group Degree Difference (regret-equal)", regretEqualScore],
];

const boxHeight = metrics.length * metricRowHeight + metricPadding * 2;

// Background box
const metricsBox = document.createElementNS(
  "http://www.w3.org/2000/svg",
  "rect"
);
metricsBox.setAttribute("x", metricBoxX - 10);
metricsBox.setAttribute("y", metricsY - 30);
metricsBox.setAttribute("width", metricBoxWidth);
metricsBox.setAttribute("height", boxHeight + 30);
metricsBox.setAttribute("stroke", "#ccc");
metricsBox.setAttribute("stroke-width", 1.5);
metricsBox.setAttribute("fill", "#f9f9f9");
metricsBox.setAttribute("rx", 8);
metricsBox.setAttribute("ry", 8);
svg.appendChild(metricsBox);

// Header
const metricsHeader = document.createElementNS(
  "http://www.w3.org/2000/svg",
  "text"
);
metricsHeader.setAttribute("x", metricBoxX);
metricsHeader.setAttribute("y", metricsY - 5);
metricsHeader.setAttribute("font-size", "16");
metricsHeader.setAttribute("font-weight", "bold");
metricsHeader.setAttribute("fill", "#333");
metricsHeader.textContent = "Fairness Metrics:";
svg.appendChild(metricsHeader);

// Metric rows
let currentY = metricsY + metricPadding + 15;
for (const [label, value] of metrics) {
  const labelText = document.createElementNS(
    "http://www.w3.org/2000/svg",
    "text"
  );
  labelText.setAttribute("x", metricBoxX);
  labelText.setAttribute("y", currentY);
  labelText.setAttribute("font-size", "12");
  labelText.setAttribute("fill", "#444");
  labelText.textContent = `${label}:`;
  svg.appendChild(labelText);

  const valueText = document.createElementNS(
    "http://www.w3.org/2000/svg",
    "text"
  );
  valueText.setAttribute("x", metricBoxX + 250);
  valueText.setAttribute("y", currentY);
  valueText.setAttribute("font-size", "12");
  valueText.setAttribute("fill", "#000");
  valueText.setAttribute("font-weight", "bold");
  valueText.textContent = `${value}`;
  svg.appendChild(valueText);

  currentY += metricRowHeight;
}
