
import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np

# Step 1: Read the data
with open('data/train.txt', 'r') as f:
    train_text = f.read()

with open('data/test.txt', 'r') as f:
    test_text = f.read()

# Step 2: Create a vocabulary
combined_text = train_text + test_text
chars = sorted(list(set(combined_text)))
char_to_int = {ch: i for i, ch in enumerate(chars)}
int_to_char = {i: ch for i, ch in enumerate(chars)}
n_vocab = len(chars)

# Step 3: Prepare the data
def text_to_sequences(text, char_to_int):
    return [char_to_int[char] for char in text]

train_data = text_to_sequences(train_text, char_to_int)
test_data = text_to_sequences(test_text, char_to_int)

seq_length = 100
dataX = []
dataY = []
for i in range(0, len(train_data) - seq_length, 1):
    seq_in = train_data[i:i + seq_length]
    seq_out = train_data[i + seq_length]
    dataX.append(seq_in)
    dataY.append(seq_out)
n_patterns = len(dataX)

X = torch.tensor(dataX, dtype=torch.float32).reshape(n_patterns, seq_length, 1)
X = X / float(n_vocab)
y = torch.tensor(dataY)

# Step 4: Define the model
class CharModel(nn.Module):
    def __init__(self):
        super(CharModel, self).__init__()
        self.lstm = nn.LSTM(1, 256, 2, batch_first=True)
        self.fc = nn.Linear(256, n_vocab)

    def forward(self, x):
        out, _ = self.lstm(x)
        out = self.fc(out[:, -1, :])
        return out

model = CharModel()

# Step 5: Train the model
optimizer = optim.Adam(model.parameters())
loss_fn = nn.CrossEntropyLoss()

for epoch in range(10):
    for i in range(0, len(X), 64):
        inputs = X[i:i+64]
        targets = y[i:i+64]

        optimizer.zero_grad()
        outputs = model(inputs)
        loss = loss_fn(outputs, targets)
        loss.backward()
        optimizer.step()

    print(f'Epoch {epoch+1}/10, Loss: {loss.item()}')

# Step 6: Export the model to ONNX
dummy_input = torch.randn(1, seq_length, 1)
torch.onnx.export(model, dummy_input, "model.onnx")

print("Model exported to model.onnx")
